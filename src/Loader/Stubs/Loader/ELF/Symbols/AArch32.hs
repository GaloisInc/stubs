{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Stubs.Loader.ELF.Symbols.AArch32 ( elfAarch32Rels ) where

import qualified Control.Exception as X
import           Control.Monad ( unless )
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe, listToMaybe )
import           Data.Word ( Word64 )

import qualified Data.ElfEdit as DE
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.LoadCommon as DMML

import qualified Stubs.Exception as AE
import qualified Stubs.Loader.Relocations as ALR
import qualified Stubs.Panic as AP

-- | Read the .rel.dyn sections from a collection of binaries and return two
-- 'Map.Map's, each mapping from relocation variable addresses to the relocation
-- types. The first 'Map.Map' only contains relocations that the verifier does
-- not (yet) support (with a string describing what sort of relocation it is),
-- while the second 'Map.Map' only contains relocations that the verifier
-- /does/ support.
elfAarch32Rels :: forall arch w f
                . ( Integral (DE.ElfWordType w)
                  , DMM.MemWidth w
                  , Foldable f )
               => f (DMB.LoadedBinary arch (DE.ElfHeaderInfo w))
               -> IO ( Map.Map (DMM.MemWord w) String
                     , Map.Map (DMM.MemWord w) ALR.RelocType
                     )
elfAarch32Rels = fmap (Map.mapEither partitionSupported)
               . F.foldlM go Map.empty
  where
    go :: Map.Map (DMM.MemWord w) (DE.RelEntry DE.ARM32_RelocationType)
       -> DMB.LoadedBinary arch (DE.ElfHeaderInfo w)
       -> IO (Map.Map (DMM.MemWord w) (DE.RelEntry DE.ARM32_RelocationType))
    go acc lb = do
      let elfHeaderInfo = DMB.originalBinary lb
      let (_, elf) = DE.getElf elfHeaderInfo

      -- NOTE: We don't currently support aarch32 binaries with .rela.dyn
      -- sections (see ticket #98)
      unless (null (DE.findSectionByName (BSC.pack ".rela.dyn") elf))
        (X.throw AE.Aarch32RelaDynUnsupported)

      return $ fromMaybe acc $ do
        relDyn <- listToMaybe $ DE.findSectionByName (BSC.pack ".rel.dyn") elf
        let relDynBytes = DE.elfSectionData relDyn
        rels <- rightToMaybe $ DE.decodeRelEntries (DE.elfData elf) relDynBytes
        let offset = fromMaybe 0 $ DMML.loadOffset $ DMB.loadOptions lb
        pure $ F.foldl' (updateMap offset) acc rels

    -- | Check whether a relocation is supported and update 'unsupported' if it
    -- is not.
    updateMap :: Word64
              -> Map.Map (DMM.MemWord w) (DE.RelEntry DE.ARM32_RelocationType)
              -> DE.RelEntry DE.ARM32_RelocationType
              -> Map.Map (DMM.MemWord w) (DE.RelEntry DE.ARM32_RelocationType)
    updateMap offset m rel =
      let addr = DMM.memWord (fromIntegral offset + fromIntegral (DE.relAddr rel)) in
      -- In each of these updates we panic if a global already exists at the
      -- address.  This should not be possible and indicates that binaries are
      -- loaded at overlapping addresses.
      Map.insertWithKey panicAddrCollision addr rel m

    panicAddrCollision addr _ _ =
      AP.panic AP.Loader
               "elfAarch32UnsupportedRels"
               ["Encoutered multiple globals at address: " ++ (show addr)]

    rightToMaybe :: Either l r -> Maybe r
    rightToMaybe = either (const Nothing) Just

    -- 'Left' indicates a relocation type is not supported, while
    -- 'Right' indicates that it is supported.
    partitionSupported :: DE.RelEntry DE.ARM32_RelocationType
                       -> Either String ALR.RelocType
    partitionSupported rel =
      case DE.relType rel of
        DE.R_ARM_ABS32    -> Right ALR.SymbolReloc
        DE.R_ARM_COPY     -> Right ALR.CopyReloc
        DE.R_ARM_GLOB_DAT -> Right ALR.SymbolReloc
        DE.R_ARM_RELATIVE -> Right ALR.RelativeReloc
        _                 -> Left $ show $ DE.relType rel
