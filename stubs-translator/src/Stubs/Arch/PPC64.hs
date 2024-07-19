{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-|
Description: Preamble Instance for PPC64
-}
module Stubs.Arch.PPC64() where
import qualified Stubs.AST as SA
import qualified What4.Interface as WI
import qualified Stubs.Preamble as SPR
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Macaw.PPC as DMP
import Data.Macaw.PPC.Symbolic ()
import Stubs.Preamble.Common( arithBinOverride, cmpBinOverride, bvIdOverride, bvExtendOverride )
import qualified Lang.Crucible.Types as LCT
import qualified Stubs.Translate.Core as STC
import qualified Data.Parameterized.NatRepr as PN
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.CFG.Expr as LCCE
import GHC.Natural (naturalToInteger)
import qualified Data.Parameterized.Map as MapF
import qualified Stubs.Translate.Intrinsic as STI
import qualified Lang.Crucible.LLVM.MemModel as LCLM

instance STC.StubsArch DMP.PPC64 where

    type instance ArchIntSize DMP.PPC64 = 32
    type instance ArchShortSize DMP.PPC64 = 16
    type instance ArchLongSize DMP.PPC64 = 64

    toCrucibleTy tyrepr = do
        case tyrepr of
            SA.StubsIntRepr -> return $ LCT.BVRepr (PN.knownNat @32)
            SA.StubsBoolRepr -> return LCT.BoolRepr
            SA.StubsUnitRepr -> return LCT.UnitRepr
            SA.StubsPointerRepr -> pure $ LCLM.LLVMPointerRepr (PN.knownNat @64)
            SA.StubsUIntRepr -> return $ LCT.BVRepr (PN.knownNat @32)
            SA.StubsLongRepr -> return $ LCT.BVRepr (PN.knownNat @64)
            SA.StubsShortRepr-> return $ LCT.BVRepr (PN.knownNat @16)
            SA.StubsULongRepr -> return $ LCT.BVRepr (PN.knownNat @64)
            SA.StubsUShortRepr-> return $ LCT.BVRepr (PN.knownNat @16)
            SA.StubsCharRepr -> pure $ LCT.BVRepr (PN.knownNat @8)
            SA.StubsUCharRepr -> pure $ LCT.BVRepr (PN.knownNat @8)
            SA.StubsAliasRepr s -> do
                env <- STC.getStubEnv
                let tymap = STC.stTyMap env
                case MapF.lookup  s tymap of
                    Just (STC.WrappedStubsTypeAliasRepr _ t) -> STC.toCrucibleTy t
                    Nothing -> error $ "missing type alias: " ++ show s
            SA.StubsIntrinsicRepr s -> do
                env <- STC.getStubEnv
                let intrinsicMap = STC.stIntrinsicMap env
                case MapF.lookup s intrinsicMap of
                    Just (STC.WrappedIntrinsicRepr _ t) -> return t
                    Nothing -> error $ "Missing intrinsic: " ++ show s

            SA.StubsTupleRepr t -> do
                internal <- STC.toCrucibleTyCtx @_ @DMP.PPC64 t
                return (LCT.StructRepr internal)

    translateLit lit = do
        let n = PN.knownNat @32
        let ln = PN.knownNat @64
        let sn = PN.knownNat @16
        let sc = PN.knownNat @8
        case lit of
            SA.BoolLit b -> LCCR.App $ LCCE.BoolLit b
            SA.UnitLit -> LCCR.App LCCE.EmptyApp
            SA.IntLit i -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit i)
            SA.LongLit i -> LCCR.App (LCCE.IntegerToBV ln $ LCCR.App $ LCCE.IntLit i)
            SA.UIntLit u -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit (naturalToInteger u))
            SA.ULongLit u -> LCCR.App (LCCE.IntegerToBV ln $ LCCR.App $ LCCE.IntLit (naturalToInteger u))
            SA.UShortLit u -> LCCR.App (LCCE.IntegerToBV sn $ LCCR.App $ LCCE.IntLit (naturalToInteger u))
            SA.ShortLit s -> LCCR.App (LCCE.IntegerToBV sn $ LCCR.App $ LCCE.IntLit s)
            SA.CharLit c -> LCCR.App (LCCE.IntegerToBV sc $ LCCR.App $ LCCE.IntLit c)
            SA.UCharLit c -> LCCR.App (LCCE.IntegerToBV sc $ LCCR.App $ LCCE.IntLit (naturalToInteger c))

instance SPR.Preamble DMP.PPC64 where
    preambleMap SA.StubsSignature{SA.sigFnName="plus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @DMP.PPC64 WI.bvAdd "plus"
    preambleMap SA.StubsSignature{SA.sigFnName="mult",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @DMP.PPC64 WI.bvMul "mult"
    preambleMap SA.StubsSignature{SA.sigFnName="minus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @DMP.PPC64 WI.bvSub "minus"
    preambleMap SA.StubsSignature{SA.sigFnName="gt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @DMP.PPC64 WI.bvSgt "gt"
    preambleMap SA.StubsSignature{SA.sigFnName="lt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @DMP.PPC64 WI.bvSlt "lt"
    preambleMap SA.StubsSignature{SA.sigFnName="eq",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @DMP.PPC64 WI.bvEq "eq"
    preambleMap SA.StubsSignature{SA.sigFnName="int",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUIntRepr), SA.sigFnRetTy=SA.StubsIntRepr} = bvIdOverride @DMP.PPC64 "int"
    preambleMap SA.StubsSignature{SA.sigFnName="uint",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr), SA.sigFnRetTy=SA.StubsUIntRepr} = bvIdOverride @DMP.PPC64 "uint"
    preambleMap SA.StubsSignature{SA.sigFnName="int_s",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsShortRepr), SA.sigFnRetTy=SA.StubsIntRepr} = bvExtendOverride @DMP.PPC64 "int_s" True
    preambleMap SA.StubsSignature{SA.sigFnName="long_i",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr), SA.sigFnRetTy=SA.StubsLongRepr} = bvExtendOverride @DMP.PPC64 "long_i" True
    preambleMap SA.StubsSignature{SA.sigFnName="short",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUShortRepr), SA.sigFnRetTy=SA.StubsShortRepr} = bvIdOverride @DMP.PPC64 "short"
    preambleMap SA.StubsSignature{SA.sigFnName="ushort",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsShortRepr), SA.sigFnRetTy=SA.StubsUShortRepr} = bvIdOverride @DMP.PPC64 "ushort"
    preambleMap SA.StubsSignature{SA.sigFnName="long",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsULongRepr), SA.sigFnRetTy=SA.StubsLongRepr} = bvIdOverride @DMP.PPC64 "long"
    preambleMap SA.StubsSignature{SA.sigFnName="ulong",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsLongRepr), SA.sigFnRetTy=SA.StubsULongRepr} = bvIdOverride @DMP.PPC64 "ulong"
    preambleMap SA.StubsSignature{SA.sigFnName="uint_s",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUShortRepr), SA.sigFnRetTy=SA.StubsUIntRepr} = bvExtendOverride @DMP.PPC64 "uint_s" False
    preambleMap SA.StubsSignature{SA.sigFnName="ulong_i",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUIntRepr), SA.sigFnRetTy=SA.StubsULongRepr} = bvExtendOverride @DMP.PPC64 "ulong_i" False

    preambleMap sig = error ("Missing implementation for preamble function:"++SA.sigFnName sig)

instance STI.OverrideArch DMP.PPC64 where
  buildOverrides = pure []
