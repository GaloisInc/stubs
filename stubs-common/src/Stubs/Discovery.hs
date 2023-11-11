{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | Functions for running the macaw code discovery on a binary
--
-- Ideally, the incremental code discovery logic can be maintained
-- entirely within this module without details leaking to other subsystems.
module Stubs.Discovery (
    discoverFunction
  ) where

import           Control.Lens ( (&), (.~) )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.Parameterized.Some as Some
import qualified Lumberjack as LJ

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Utils.IncComp as DMUI

import qualified Stubs.Loader.BinaryConfig as ALB
import qualified Stubs.Diagnostic as AD

-- | We pass this log function to macaw to wrap discovery events in a custom
-- wrapper that we stream out with the rest of our diagnostics.
--
-- The default logger in macaw just prints to stderr, which is not very helpful
logDiscoveryEvent
  :: ( MonadIO m
     , DMM.MemWidth w
     , DMC.ArchConstraints arch
     , w ~ DMC.RegAddrWidth (DMC.ArchReg arch) )
  => LJ.LogAction IO AD.Diagnostic
  -> DMD.AddrSymMap w
  -> DMD.DiscoveryEvent arch
  -> m ()
logDiscoveryEvent logAction symMap evt =
  liftIO $ LJ.writeLog logAction (AD.DiscoveryEvent symMap evt)

-- | Run code discovery on a single function at the given address, streaming
-- out diagnostics that provide indications of progress. See
-- @Note [Incremental code discovery]@ in "Ambient.Extensions".
discoverFunction ::
  (MonadIO m, DMB.BinaryLoader arch binFmt) =>
  LJ.LogAction IO AD.Diagnostic ->
  DMA.ArchitectureInfo arch ->
  ALB.LoadedBinaryPath arch binFmt ->
  -- ^ Binary in which the function is defined
  DMC.ArchSegmentOff arch ->
  -- ^ The function address to discover
  m (Some.Some (DMD.DiscoveryFunInfo arch))
discoverFunction logAction archInfo loadedBinaryPath addr = do
  let mem = DMB.memoryImage $ ALB.lbpBinary loadedBinaryPath
  let symMap = ALB.lbpAddrSymMap loadedBinaryPath
  let pltEntryPoints = ALB.lbpTrustedPltEntryPoints loadedBinaryPath
  let s0 = DMD.emptyDiscoveryState mem symMap archInfo
             & DMD.trustedFunctionEntryPoints .~ pltEntryPoints
  DMA.withArchConstraints archInfo $ do
    (_state, funInfo) <-
      DMUI.processIncCompLogs (logDiscoveryEvent logAction symMap) $ DMUI.runIncCompM $ do
        DMUI.incCompLog $ DMD.ReportAnalyzeFunction addr
        let discoveryOpts = DMD.defaultDiscoveryOptions
        res@(_, Some.Some (funInfo)) <- DMUI.liftIncComp id $
          DMD.discoverFunction discoveryOpts addr DMD.UserRequest s0 []
        DMUI.incCompLog $ DMD.ReportAnalyzeFunctionDone funInfo
        pure res
    pure funInfo
