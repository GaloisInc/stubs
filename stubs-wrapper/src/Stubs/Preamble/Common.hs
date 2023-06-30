{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
module Stubs.Preamble.Common (
    arithBinOverride,
    cmpBinOverride,
    bvIdOverride,
    bvExtendOverride
) where 


import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Types as LCT
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Parameterized.Context as Ctx
import Control.Monad.IO.Class
import Data.Text
import qualified Stubs.Translate.Core as STC
import qualified Data.Parameterized.NatRepr as PN
import GHC.TypeLits (KnownNat)

-- binary arithmetic operations, parametrized over operations
arithBinOverride :: forall arch bak solver scope st fs w p ext sym. (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym, STC.StubsArch arch, w ~ STC.ArchIntSize arch) =>
                (sym -> WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.SymBV sym w)) -> Text -> bak -> LCS.Override p sym ext ((LCT.EmptyCtx LCT.::> LCT.BVType w) LCT.::> LCT.BVType w) (LCT.BVType w)
arithBinOverride op name bak = LCS.mkOverride' (WF.functionNameFromText name) (LCT.BVRepr (PN.knownNat @(STC.ArchIntSize arch))) (do
    LCS.RegMap args <-  LCS.getOverrideArgs
    let sym = LCB.backendGetSym bak
    execArithBin @arch sym op args
  )

cmpBinOverride :: forall arch bak solver scope st fs w p ext sym. (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym, STC.StubsArch arch, w ~ STC.ArchIntSize arch) =>
                (sym -> WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.Pred sym)) -> Text -> bak -> LCS.Override p sym ext ((LCT.EmptyCtx LCT.::> LCT.BVType w) LCT.::> LCT.BVType w) LCT.BoolType
cmpBinOverride op name bak = LCS.mkOverride' (WF.functionNameFromText name) LCT.BoolRepr (do
    LCS.RegMap args <-  LCS.getOverrideArgs
    let sym = LCB.backendGetSym bak
    execCmpBin @arch sym op args
  )

bvIdOverride :: forall arch bak solver scope st fs w p ext sym. (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym, STC.StubsArch arch, 1 PN.<= w, KnownNat w) =>
                Text -> bak -> LCS.Override p sym ext (LCT.EmptyCtx LCT.::> LCT.BVType w) (LCT.BVType w)
bvIdOverride name bak = LCS.mkOverride' (WF.functionNameFromText name) (LCT.BVRepr (PN.knownNat @w)) (do
    LCS.RegMap args <-  LCS.getOverrideArgs
    let sym = LCB.backendGetSym bak
    execId @arch sym args
  )

bvExtendOverride :: forall arch bak solver scope st fs w1 w2 p ext sym. (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym, STC.StubsArch arch,
                    1 PN.<= w1, w1 PN.+1 PN.<= w2, KnownNat w2, 1 PN.<= w2) =>
                Text -> Bool -> bak -> LCS.Override p sym ext (LCT.EmptyCtx LCT.::> LCT.BVType w1) (LCT.BVType w2)
bvExtendOverride name signed bak = LCS.mkOverride' (WF.functionNameFromText name) (LCT.BVRepr (PN.knownNat @w2)) (do
    LCS.RegMap args <-  LCS.getOverrideArgs
    let sym = LCB.backendGetSym bak
    execExtend @arch sym signed args
  )

execId :: forall arch sym m w . (MonadIO m, WI.IsExprBuilder sym, (STC.StubsArch arch), 1 PN.<= w, KnownNat w) =>
            sym -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCT.BVType w) ->  m (LCS.RegValue sym (LCT.BVType w))
execId _ (Ctx.Empty Ctx.:> bv1) = do 
    return $ LCS.regValue bv1

-- Take sym, arithmetic operation, and args, and performs operation 
execArithBin ::forall arch sym m w . (MonadIO m, WI.IsExprBuilder sym, (STC.StubsArch arch), w ~ STC.ArchIntSize arch) =>
            sym -> (sym -> WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.SymBV sym w)) -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCT.BVType w Ctx.::> LCT.BVType w) ->  m (LCS.RegValue sym (LCT.BVType w))
execArithBin sym op (Ctx.Empty Ctx.:> bv1 Ctx.:> bv2) = do
  liftIO $ op sym (LCS.regValue bv1) (LCS.regValue bv2)

execCmpBin :: forall arch sym m w . (MonadIO m, WI.IsExprBuilder sym, (STC.StubsArch arch), w ~ STC.ArchIntSize arch) =>
            sym ->(sym -> WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.Pred sym) )-> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCT.BVType w Ctx.::> LCT.BVType w) ->  m (LCS.RegValue sym LCT.BoolType)
execCmpBin sym op (Ctx.Empty Ctx.:> bv1 Ctx.:> bv2) = do
  liftIO $ op sym (LCS.regValue bv1) (LCS.regValue bv2)

execExtend :: forall arch sym m w1 w2 . (MonadIO m, WI.IsExprBuilder sym, (STC.StubsArch arch), 1 PN.<= w1, w1 PN.+1 PN.<= w2, KnownNat w2 ) =>
            sym -> Bool -> Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx Ctx.::> LCT.BVType w1) ->  m (LCS.RegValue sym (LCT.BVType w2))
execExtend sym signed (Ctx.Empty Ctx.:> bv) = do 
  if signed then liftIO $ WI.bvSext sym (PN.knownNat @w2) (LCS.regValue bv) else liftIO $ WI.bvZext sym (PN.knownNat @w2) (LCS.regValue bv)