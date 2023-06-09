{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Stubs.EntryPoint
  ( EntryPoint(..)
  , resolveEntryPointAddrOff
  ) where

import qualified Control.Monad.Catch as CMC
import qualified Data.Map.Strict as Map
import Data.Text ( Text )
import Data.Word ( Word64 )

import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.BinaryLoader.ELF as DMBE
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified What4.FunctionName as WF

import qualified Stubs.Exception as AE
import qualified Stubs.Loader.BinaryConfig as ALB

-- | Where to begin simulation.
data EntryPoint
  = DefaultEntryPoint
    -- ^ Begin simulation at the default entry point. For now, this is the
    -- main() function. See @Note [Entry Point]@ for why.
  | EntryPointName Text
    -- ^ Begin simulation at the function with the given name.
  | EntryPointAddr Word64
    -- ^ Begin simulation at the function with the given address.
  deriving Show

-- | Resolve an 'EntryPoint' to an address offset. If the entry point is
-- a function name, try to look up the corresponding address as described in
-- @Note [Incremental code discovery]@ in "Ambient.Extensions". If resolution
-- fails, this function will throw an exception.
resolveEntryPointAddrOff ::
  forall m arch binFmt w.
  ( CMC.MonadThrow m
  , DMM.MemWidth (DMC.ArchAddrWidth arch)
  , DMB.BinaryLoader arch binFmt
  , w ~ DMC.ArchAddrWidth arch
  ) =>
  ALB.BinaryConfig arch binFmt ->
  EntryPoint ->
  m (DMM.MemSegmentOff w)
resolveEntryPointAddrOff binConf ep =
  case ep of
    EntryPointAddr addr -> resolveAddr $ DMM.memWord addr
    DefaultEntryPoint   -> resolveEntryPointNamed "main"
    EntryPointName n    -> resolveEntryPointNamed $ WF.functionNameFromText n
  where
    resolveEntryPointNamed :: WF.FunctionName -> m (DMM.MemSegmentOff w)
    resolveEntryPointNamed n =
      case Map.lookup n (ALB.bcMainBinarySymbolMap binConf) of
        Just addr -> resolveAddr addr
        Nothing   -> CMC.throwM $ AE.NamedEntryPointAddrLookupFailure n

    resolveAddr :: DMM.MemWord w -> m (DMM.MemSegmentOff w)
    resolveAddr addr =
      let mem = DMB.memoryImage
              $ ALB.lbpBinary
              $ ALB.mainLoadedBinaryPath binConf in
      case DMBE.resolveAbsoluteAddress mem addr of
        Just seg -> pure seg
        Nothing -> CMC.throwM $ AE.EntryPointAddrOffResolutionFailure addr
