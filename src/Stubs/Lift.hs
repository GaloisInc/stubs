{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Stubs.Lift ( discoveredFunName, liftDiscoveredFunction ) where

import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Parameterized.Context as Ctx
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as DT

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified What4.FunctionName as WF
import qualified What4.ProgramLoc as WP

-- | Construct a 'WF.FunctionName' for the given discovered function
--
-- This uses the associated symbol, if any. Otherwise, it will synthesize a name
-- based on the function address
discoveredFunName
  :: (DMM.MemWidth (DMC.ArchAddrWidth arch))
  => DMD.DiscoveryFunInfo arch ids
  -> WF.FunctionName
discoveredFunName dfi =
  case DMD.discoveredFunSymbol dfi of
    Just bytes ->
      -- NOTE: This bytestring is not really guaranteed to be in any particular
      -- encoding, so this conversion to text could fail
      WF.functionNameFromText (DT.pack (BSC.unpack bytes))
    Nothing -> WF.functionNameFromText (DT.pack (show (DMD.discoveredFunAddr dfi)))

-- | Convert machine addresses into Crucible positions
--
-- When possible, we map to the structured 'WP.BinaryPos' type. However, some
-- 'DMM.MemSegmentOff' cannot be mapped to an absolute position (e.g., some
-- addresses from shared libraries are in non-trivial segments). In those cases,
-- we map to the unstructured 'WP.Others' with a sufficiently descriptive string.
--
-- A more sophisticated program location data type could make this more flexible
machineAddressToCruciblePosition
  :: (DMM.MemWidth (DMC.ArchAddrWidth arch))
  => proxy arch
  -> FilePath
  -> DMC.ArchSegmentOff arch
  -> WP.Position
machineAddressToCruciblePosition _ imageName segOff =
  case DMM.segoffAsAbsoluteAddr segOff of
    Just mw -> WP.BinaryPos (DT.pack imageName) (fromIntegral mw)
    Nothing -> WP.OtherPos (DT.pack imageName <> DT.pack ": " <> DT.pack (show segOff))

-- | Lift a discovered macaw function into a Crucible CFG suitable for symbolic execution
liftDiscoveredFunction
  :: forall m arch ids
   . (MonadIO m, DMM.MemWidth (DMC.ArchAddrWidth arch))
  => LCF.HandleAllocator
  -> String
  -> DMS.MacawSymbolicArchFunctions arch
  -> DMD.DiscoveryFunInfo arch ids
  -> m (LCCC.SomeCFG (DMS.MacawExt arch) (Ctx.EmptyCtx Ctx.::> DMS.ArchRegStruct arch) (DMS.ArchRegStruct arch))
liftDiscoveredFunction hdlAlloc imageName symArchFuns dfi = do
  let funName = discoveredFunName dfi
  let posFn = machineAddressToCruciblePosition (Proxy @arch) imageName
  liftIO $ DMS.mkFunCFG symArchFuns hdlAlloc funName posFn dfi
