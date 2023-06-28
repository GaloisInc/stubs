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
    preambleMap SA.StubsSignature{SA.sigFnName="plus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @DMX.X86_64 WI.bvAdd
    preambleMap SA.StubsSignature{SA.sigFnName="mult",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @DMX.X86_64 WI.bvMul
    preambleMap SA.StubsSignature{SA.sigFnName="minus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @DMX.X86_64 WI.bvSub
    preambleMap SA.StubsSignature{SA.sigFnName="gt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @DMX.X86_64 WI.bvSgt
    preambleMap SA.StubsSignature{SA.sigFnName="lt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @DMX.X86_64 WI.bvSlt
    preambleMap SA.StubsSignature{SA.sigFnName="eq",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @DMX.X86_64 WI.bvEq
    preambleMap _ = error ""

-- binary arithmetic operations, parametrized over operations
arithBinOverride :: forall arch bak solver scope st fs w p ext sym. (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym, DMS.SymArchConstraints arch, w ~ DMC.ArchAddrWidth arch) =>
                (sym -> WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.SymBV sym w)) -> bak -> LCS.Override p sym ext ((LCT.EmptyCtx LCT.::> LCT.BVType w) LCT.::> LCT.BVType w) (LCT.BVType w)
arithBinOverride op bak = LCS.mkOverride' (WF.functionNameFromText "plus") (LCT.BVRepr (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch))) (do
    LCS.RegMap args <-  LCS.getOverrideArgs
    let sym = LCB.backendGetSym bak
    execArithBin @arch sym op args
  )

cmpBinOverride :: forall arch bak solver scope st fs w p ext sym. (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym, DMS.SymArchConstraints arch, w ~ DMC.ArchAddrWidth arch) =>
                (sym -> WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.Pred sym)) -> bak -> LCS.Override p sym ext ((LCT.EmptyCtx LCT.::> LCT.BVType w) LCT.::> LCT.BVType w) LCT.BoolType
cmpBinOverride op bak = LCS.mkOverride' (WF.functionNameFromText "plus") LCT.BoolRepr (do
    LCS.RegMap args <-  LCS.getOverrideArgs
    let sym = LCB.backendGetSym bak
    execCmpBin @arch sym op args
  )

-- Take sym, arithmetic operation, and args, and performs operation 
execArithBin ::forall arch sym m w . (MonadIO m, WI.IsExprBuilder sym, (DMS.SymArchConstraints arch), w ~ DMC.ArchAddrWidth arch) =>
            sym -> (sym -> WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.SymBV sym w)) -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCT.BVType w Ctx.::> LCT.BVType w) ->  m (LCS.RegValue sym (LCT.BVType w))
execArithBin sym op (Ctx.Empty Ctx.:> bv1 Ctx.:> bv2) = do
  liftIO $ op sym (LCS.regValue bv1) (LCS.regValue bv2)

execCmpBin :: forall arch sym m w . (MonadIO m, WI.IsExprBuilder sym, (DMS.SymArchConstraints arch), w ~ DMC.ArchAddrWidth arch) =>
            sym ->(sym -> WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.Pred sym) )-> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCT.BVType w Ctx.::> LCT.BVType w) ->  m (LCS.RegValue sym LCT.BoolType)
execCmpBin sym op (Ctx.Empty Ctx.:> bv1 Ctx.:> bv2) = do
  liftIO $ op sym (LCS.regValue bv1) (LCS.regValue bv2)