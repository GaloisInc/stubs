{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.Loader.ELF.PLTStubDetector (
    pltStubSymbols
  ) where

import qualified Control.Monad.Catch as CMC
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit as DE
import qualified Data.ElfEdit.Prim as DEP
import           Data.Foldable (Foldable(..))
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe, listToMaybe)
import           Data.Word (Word32)

import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.LoadCommon as MML

import qualified Stubs.ABI as AA
import qualified Stubs.Exception as AE
import qualified Stubs.Loader.ELF.Symbols as ALES
import qualified Stubs.Loader.Versioning as ALV

-- | A wrapper type to make it easier to extract both Rel and Rela entries
data SomeRel tp where
  SomeRel :: [r tp] -> (r tp -> Word32) -> SomeRel tp

-- | Match up names to PLT stub entries in an ELF binary.
--
-- Calls to functions in shared libraries are issued through PLT stubs. These
-- are short sequences included in the binary by the compiler that jump to the
-- *real* function implementation in the shared library via the Global Offset
-- Table.  The GOT is populated by the dynamic loader.
--
-- See Note [PLT Stub Names] for details
pltStubSymbols
  :: forall w proxy reloc arch
   . ( w ~ DEP.RelocationWidth reloc
     , w ~ DMC.ArchAddrWidth arch
     , Integral (DEP.ElfWordType w)
     , DEP.IsRelocationType reloc
     , DMM.MemWidth w
     )
  => AA.ABI
  -> proxy reloc
  -> DMB.LoadedBinary arch (DE.ElfHeaderInfo w)
  -> Map.Map (DMM.MemWord w) ALV.VersionedFunctionName
pltStubSymbols abi _ loadedBinary = Map.fromList $ fromMaybe [] $ do
  let elfHeaderInfo = DMB.originalBinary loadedBinary
  let loadOptions = DMB.loadOptions loadedBinary
  let (_, elf) = DE.getElf elfHeaderInfo
  let phdrs = DE.headerPhdrs elfHeaderInfo
  let elfBytes = DE.headerFileContents elfHeaderInfo

  vam <- DEP.virtAddrMap elfBytes phdrs
  rawDynSec <- listToMaybe (DE.findSectionByName (BSC.pack ".dynamic") elf)

  let dynBytes = DE.elfSectionData rawDynSec
  dynSec <- case DEP.dynamicEntries (DE.elfData elf) (DE.elfClass elf) dynBytes of
    Left _dynErr -> Nothing
    Right dynSec -> return dynSec

  vdefm <- case DEP.dynVersionDefMap dynSec vam of
    Left _dynErr -> Nothing
    Right vm -> return vm

  vreqm <- case DEP.dynVersionReqMap dynSec vam of
    Left _dynErr -> Nothing
    Right vm -> return vm

  let pltAddrs = case extractPltAddrs dynSec vam vdefm vreqm loadOptions elf of
        Nothing -> []
        Just addrs -> addrs

  let pltGotAddrs = case extractPltGotAddrs dynSec vam vdefm vreqm loadOptions elf of
        Nothing -> []
        Just addrs -> addrs
  return (pltAddrs ++ pltGotAddrs)
  where
    pltStubAddress dynSec vam vdefm vreqm getRelSymIdx accum rel
      | Right (symtabEntry, versionedVal) <- DEP.dynSymEntry dynSec vam vdefm vreqm (getRelSymIdx rel) =
          let versym = ALV.VerSym { ALV.versymSymbol = ALES.symtabEntryFunctionName symtabEntry
                                  , ALV.versymVersion = ALES.versionTableValueToSymbolVersion versionedVal
                                  } in
          versym : accum
      | otherwise = accum

    buildAssocList nameRelaMap baseAddr stubSize loadOptions =
      let loadOffset = toInteger $ fromMaybe 0 (MML.loadOffset loadOptions) in
      [ (DMM.memWord (fromIntegral addr), versym)
      | (idx, versym) <- nameRelaMap
      , let addr = loadOffset + baseAddr + idx * stubSize
      ]

    -- Build assoc list from addresses of stubs in .plt to function names
    extractPltAddrs dynSec vam vdefm vreqm loadOptions elf = do
      SomeRel rels getRelSymIdx <- case DEP.dynPLTRel @reloc dynSec vam of
        Right (DEP.PLTRela relas) -> return (SomeRel relas DEP.relaSym)
        Right (DEP.PLTRel rels) -> return (SomeRel rels DEP.relSym)
        _ -> Nothing
      let revNameRelaMap = foldl' (pltStubAddress dynSec vam vdefm vreqm getRelSymIdx) [] rels
      let nameRelaMap = zip [0..] (reverse revNameRelaMap)
      pltSec <- listToMaybe (DE.findSectionByName (BSC.pack ".plt") elf)
      let pltBase = DE.elfSectionAddr pltSec
      -- 'pltSize' is the size of the .plt function and 'pltStubSize' is
      -- the size of each plt stub in bytes.  These values were obtained via
      -- examination of binaries in the wild.
      let (pltSize, pltStubSize) = case abi of
                                     AA.AArch32Linux -> (20, 12)
                                     AA.X86_64Linux -> (16, 16)
      return $ buildAssocList nameRelaMap (pltSize + toInteger pltBase) pltStubSize loadOptions

    -- Build assoc list from addresses of stubs in .plt.got to function names
    extractPltGotAddrs dynSec vam vdefm vreqm loadOptions elf = do
      relsGot <- case DEP.dynRelaEntries @reloc dynSec vam of
        Right relas -> return relas
        Left _ -> Nothing
      let revNameRelaMapGot = foldl' (pltStubAddress dynSec vam vdefm vreqm DEP.relaSym) [] relsGot
      let nameRelaMapGot = zip [0..] (reverse revNameRelaMapGot)

      pltGotSec <- listToMaybe (DE.findSectionByName (BSC.pack ".plt.got") elf)
      let pltGotBase = DE.elfSectionAddr pltGotSec
      -- 'pltGotStubSize' is the size in bytes of each stub in .plt.got.  These
      -- values were obtained via examination of binaries in the wild.
      pltGotStubSize <-
            case abi of
              AA.AArch32Linux ->
                -- It's unclear whether or not this case is possible.  It
                -- doesn't appear in aarch32 ELF reference documents and the
                -- use of function pointers doesn't appear to generate .plt.got
                -- stubs on aarch32.  If we do encounter one of these stubs it
                -- in the wild then all we need to do is add the appropriate
                -- offset here and the rest of the code should work.
                CMC.throwM AE.Aarch32BinaryHasPltGot
              AA.X86_64Linux -> return 8
      return $ buildAssocList nameRelaMapGot (toInteger pltGotBase) pltGotStubSize loadOptions

{- Note [PLT Stub Names]

In a dynamically linked binary, the compiler issues calls to shared library
functions by jumping to a PLT stub. The PLT stub jumps to an address taken from
the Global Offset Table (GOT), which is populated by the dynamic loader based on
where the shared library is mapped into memory.

These PLT stubs are not inherently assigned names, but we would like to have
sensible names that we can use to specify overrides for dynamically-linked
functions (e.g., libc calls). For example, we might want to install overrides
for both @malloc@ and @malloc\@plt@ (with the latter representing a call to a
dynamically linked library function).

PLT stubs do not have their own names in any symbol table. Instead, entries in
the Global Offset Table have names in the form of dynamic PLT relocations.  We
get those from elf-edit via the 'DEP.dynPLTRel' function. Note that these
relocations do not have their own directly associated names; instead, there is a
list of rela entries and a separate list of symbols. The list of rela entries
contains function relocations while the list of dynamic symbols
('DEP.dynSymEntry') contains both function and object symbols. To align them, we
must just discard the non-function entries. We do this by checking if the
current symbol entry is of function type; if it is not, we just grab the next
function symbol in the list.

That step gives us names for global offset table entries, but *not* names for
PLT stubs. We rely on the fact that the list of PLT stubs is in the same order
as the list of global offset table entries.  The previous step gives us the
*index* of each entry and a name for that entry. To get the name of the PLT stub
itself, we just compute the relevant offset from the base of the .plt
section.  Each PLT stub is 16 bytes on most architectures. For example, on
x86_64 The address of the PLT stub of an entry is @addrOf(.plt) + 16 * idx@.

-}
