module Stubs.Loader.BinaryConfig
  ( BinaryConfig(..)
  , mainLoadedBinaryPath
  , LoadedBinaryPath(..)
  , lbpAddrSymMap
  , lbpTrustedPltEntryPoints
  ) where

import qualified Data.ByteString as BS
import qualified Data.List.NonEmpty as NEL
import qualified Data.Text.Encoding as DTE
import qualified Data.Vector.NonEmpty as NEV
import qualified Data.Map.Strict as Map

import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.BinaryLoader.ELF as DMBE
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified What4.FunctionName as WF

import qualified Stubs.Loader.Relocations as ALR
import qualified Stubs.Loader.Versioning as ALV
import qualified Stubs.Panic as AP

-- | All of the loaded binaries along with information about their file paths,
-- function symbols, and PLT stubs. Retrieving this information requires
-- functionality that is specific to a particular file format (e.g., ELF), so
-- this data type provides a place to store this information so that it can be
-- used without hard-coding a particular file format.
data BinaryConfig arch binFmt = BinaryConfig {
    bcBinaries :: NEV.NonEmptyVector (LoadedBinaryPath arch binFmt)
  -- ^ A vector of all loaded binaries, where the binary at index 0 is the main
  -- binary, index 1 is the first shared library, index 2 is the second shared
  -- library, and so on. See @Note [Address offsets for shared libraries]@
  -- in "Ambient.Loader.LoadOffset".

  , bcMainBinarySymbolMap :: Map.Map WF.FunctionName (DMM.MemWord (DMC.ArchAddrWidth arch))
  -- ^ Maps the function symbols of each entry point function in the
  -- 'mainBinary' to their addresses. This is used to determine the address of
  -- the starting entry point. See @Note [Incremental code discovery]@ in
  -- "Ambient.Extensions".

  , bcDynamicFuncSymbolMap :: Map.Map ALV.VersionedFunctionName (DMM.MemWord (DMC.ArchAddrWidth arch))
  -- ^ Maps the names of dynamic functions in each binary to their addresses.
  -- This is used to determine the address that a PLT stub should jump to.
  -- See @Note [Incremental code discovery]@ in "Ambient.Extensions".

  , bcDynamicGlobalVarAddrs :: Map.Map ALV.VersionedGlobalVarName (DMM.MemWord (DMC.ArchAddrWidth arch))
  -- ^ Maps the names of exported global variables in each binary to their
  -- addresses.  This is used to compute relocations in dynamically linked
  -- programs.

  , bcPltStubs :: Map.Map (DMM.MemWord (DMC.ArchAddrWidth arch)) ALV.VersionedFunctionName
  -- ^ Maps the addresses of PLT stub in each binary and shared library to
  -- their corresponding function names. See @Note [PLT stub names]@ in
  -- "Data.Macaw.Memory.ElfLoader.PLTStubs" in @macaw-base@.
  --
  -- Note that this is the same thing as the union of all the 'lbpPltStubs' in
  -- each of the binaries in 'bcBinaries'. We cache the result in this field so
  -- that we can more readily simulate PLT calls that cross binary boundaries.
  --
  -- Putting the address of every PLT stub from all binaries' address spaces
  -- into a single map is somewhat delicate. This happens to work today since
  -- we ensure that the address spaces in each binary are disjoint from each
  -- other (see @Note [Address offsets for shared libraries]@ in
  -- "Ambient.Loader.LoadOffset" for the details). However, we will want to
  -- support more flexible memory layouts such as ASLR in the future. In
  -- those sorts of layouts, we would run the risk of PLT stub addresses from
  -- different address spaces being mapped to the same 'DMM.MemWord',
  -- which will make a 'Map.Map' insufficient means of storage. See #86.

  , bcUnsuportedRelocations :: Map.Map (DMM.MemWord (DMC.ArchAddrWidth arch)) String
  -- ^ A mapping of unsupported relocations.  Maps addresses to the names of
  -- unsupported relocation types.  This allows the verifier to simulate
  -- programs containing unsupported relocation types and throw an error only
  -- if one of those relocations is read from.  This is a mapping to strings
  -- instead of relocation types because holding relocations in this map
  -- introduces IsRelocationType constraints that are difficult to fulfill
  -- when a function takes this underlying map but no binaries are loaded
  -- (such as when running crucible syntax override tests).

  , bcSupportedRelocations :: Map.Map (DMM.MemWord (DMC.ArchAddrWidth arch)) ALR.RelocType
  -- ^ A mapping of supported relocations. Maps addresses to relocation types.
  -- See also 'bcUnsuportedRelocations', which contains the rest of the
  -- relocations.
  }

-- | A loaded binary, along with the file path from which it was loaded and
-- a map of all its entry point functions.
data LoadedBinaryPath arch binFmt = LoadedBinaryPath {
    lbpBinary :: DMB.LoadedBinary arch binFmt
  -- ^ The loaded binary.

  , lbpPath :: FilePath
  -- ^ The path the 'lbpBinary' was loaded from.

  , lbpEntryPoints :: Map.Map (DMC.ArchSegmentOff arch) (NEL.NonEmpty ALV.VersionedFunctionName)
  -- ^ This maps the entry point addresses in the 'lbpBinary' to their
  -- corresponding function names. Note that a single function address can have
  -- multiple symbol names, hence the use of 'NEL.NonEmpty'. This information is
  -- used for two purposes:
  --
  -- * Seeding code discovery (see "Ambient.Discovery"), and
  --
  -- * Looking up the names of functions in order to check if they have
  --   user-supplied overrides (see @Note [Incremental code discovery]@ in
  -- "Ambient.Extensions").

  -- TODO: Instead of threading around this information as a separate field in
  -- LoadedBinaryPath, we could retrieve it from the LoadedBinary directly by
  -- using the macaw-loader API. Unfortunately, macaw-loader only supports
  -- entry points from static symbol tables at present (see
  -- https://github.com/GaloisInc/macaw-loader/issues/12), so we would have to
  -- fix this issue upstream first.

  , lbpGlobalVars :: Map.Map BS.ByteString (DMM.MemWord (DMC.ArchAddrWidth arch))
  -- ^ This maps the names of global variables in the 'lbpBinary' to their
  -- corresponding addresses. This is used to power the
  -- @get-global-pointer-named@ override.

  , lbpPltStubs :: Map.Map (DMM.MemWord (DMC.ArchAddrWidth arch)) ALV.VersionedFunctionName
  -- ^ Maps the addresses of PLT stubs in the binary to their corresponding
  -- function names. See @Note [PLT stub names]@ in
  -- "Data.Macaw.Memory.ElfLoader.PLTStubs" in @macaw-base@.
  }

-- | Convert the 'lbpEntryPoints' in a 'LoadedBinaryPath' to an
-- 'DMD.AddrSymMap'. This is accomplished by taking the first symbol name
-- associated with each function address and converting it to a @ByteString@.
--
-- This function is used exclusively for the benefit of @macaw@'s code
-- discovery, which consults the 'DMD.AddrSymMap' for logging purposes. As
-- such, it's OK to drop all of the symbol names associated with each function
-- address except for the first name. The worst thing that can happen is that
-- @macaw@'s code discovery logs might print out a function name that you
-- weren't expecting.
lbpAddrSymMap :: LoadedBinaryPath arch binFmt -> DMD.AddrSymMap (DMC.ArchAddrWidth arch)
lbpAddrSymMap = fmap (DTE.encodeUtf8 . WF.functionName . ALV.versymSymbol . NEL.head) . lbpEntryPoints

-- | Given a 'LoadedBinaryPath', construct a map of trusted entry points
-- consisting of the addresses of the binary's PLT stubs.
--
-- Because we perform incremental code discovery (see
-- @Note [Incremental code discovery]@ in "Ambient.Extensions"), we usually do
-- not need to mark any functions as trusted entry points, since most of the
-- time it suffices to perform code discovery on a function right after
-- invoking it in @macaw@. However, this only works if @macaw@ is able to
-- accurately infer what parts of the binary are actually functions. As
-- noted in <https://github.com/GaloisInc/macaw/issues/285>, @macaw@ fails to
-- realize that PLT stubs are functions when they are entered via tail calls,
-- which in turn prevents us from applying overrides to these sorts of PLT
-- stubs.
--
-- Our workaround to this problem is to simply add all of the PLT stubs for a
-- particular binary to the set of 'DMD.trustedFunctionEntryPoints' before
-- running code discovery. This is sufficient to make code discovery go the
-- extra mile to analyze each PLT stub and mark them as functions, ensuring
-- that tail calls into these PLT stubs will work as expected.
--
-- If @macaw@ improved its global fixed-point analysis, we might not need this
-- workaround. See <https://github.com/GaloisInc/macaw/issues/298> for more
-- details.
lbpTrustedPltEntryPoints ::
  DMB.BinaryLoader arch binFmt =>
  LoadedBinaryPath arch binFmt ->
  Map.Map (DMC.ArchSegmentOff arch) DMD.NoReturnFunStatus
lbpTrustedPltEntryPoints loadedBinaryPath =
    Map.fromList
  $ map (\addr ->
          case DMBE.resolveAbsoluteAddress mem addr of
            Just segOff -> (segOff, DMD.MayReturnFun)
            Nothing -> AP.panic AP.Loader "lbpTrustedPltEntryPoints"
                         ["Failed to resolve function address: " ++ show addr])
  $ Map.keys
  $ lbpPltStubs loadedBinaryPath
  where
    mem = DMB.memoryImage $ lbpBinary loadedBinaryPath

-- | Retrieve the main binary—that is, the binary at index 0 of
-- 'bcBinaries'.
mainLoadedBinaryPath :: BinaryConfig arch binFmt -> LoadedBinaryPath arch binFmt
mainLoadedBinaryPath = NEV.head . bcBinaries
