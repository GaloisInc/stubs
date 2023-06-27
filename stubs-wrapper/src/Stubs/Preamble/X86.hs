{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Stubs.Preamble.X86 where 
import qualified Stubs.AST as SA
import qualified Data.Macaw.X86 as DMX
import qualified What4.Interface as WI
import qualified Stubs.Preamble as SPR
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.Simulator as LCS
import Control.Monad.IO.Class
import qualified Lang.Crucible.Types as LCT
import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.Backend as LCB
import qualified What4.FunctionName as WF
import Data.Macaw.X86.ArchTypes ()
import Data.Macaw.X86.Symbolic ()

instance SPR.Preamble DMX.X86_64 where 
    preambleMap SA.StubsSignature{SA.sigFnName="plus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = plusOverride @DMX.X86_64
    preambleMap _ = error ""

execPlus :: forall arch sym m w . (MonadIO m, WI.IsExprBuilder sym, (DMS.SymArchConstraints arch), w ~ DMC.ArchAddrWidth arch) => 
            sym -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCT.BVType w Ctx.::> LCT.BVType w) ->  m (LCS.RegValue sym (LCT.BVType w))
execPlus sym (Ctx.Empty Ctx.:> bv1 Ctx.:> bv2) = do
  liftIO $ WI.bvAdd sym (LCS.regValue bv1) (LCS.regValue bv2)

--override action needs to setup argument and return handling in order to be seamlessly called as if by callOverride, so it can be registered to a handle directly
stubsPlus :: forall arch bak solver scope st fs sym w p ext r ret. (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym,DMS.SymArchConstraints arch, w ~ DMC.ArchAddrWidth arch) => 
             bak -> LCS.OverrideSim p sym ext r (LCT.EmptyCtx LCT.::> LCT.BVType w LCT.::> LCT.BVType w) ret (LCS.RegValue sym (LCT.BVType w))
stubsPlus bak = do
  LCS.RegMap args <-  LCS.getOverrideArgs
  let sym = LCB.backendGetSym bak
  execPlus @arch sym args 

plusOverride :: forall arch bak solver scope st fs w p ext sym. (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym, DMS.SymArchConstraints arch, w ~ DMC.ArchAddrWidth arch) => 
                bak -> LCS.Override p sym ext ((LCT.EmptyCtx LCT.::> LCT.BVType w) LCT.::> LCT.BVType w) (LCT.BVType w)
plusOverride bak = LCS.mkOverride' (WF.functionNameFromText "plus") retRepr (stubsPlus @arch bak)
    where
        retRepr = LCT.BVRepr (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch))