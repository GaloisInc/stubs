{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
Description: Preamble Instance for AArch32
-}
module Stubs.Arch.AArch32() where
import qualified Stubs.AST as SA
import qualified What4.Interface as WI
import qualified Stubs.Preamble as SPR
import qualified Data.Parameterized.Context as Ctx
import qualified SemMC.Architecture.AArch32 as SAA
import Data.Macaw.AArch32.Symbolic ()
import Stubs.Preamble.Common ( arithBinOverride, cmpBinOverride, bvIdOverride,bvExtendOverride )
import qualified Stubs.Translate.Core as STC
import qualified Lang.Crucible.Types as LCT
import qualified Data.Parameterized.NatRepr as PN
import qualified Lang.Crucible.CFG.Expr as LCCE
import qualified Lang.Crucible.CFG.Reg as LCCR
import GHC.Natural (naturalToInteger)
import qualified Data.Parameterized.Map as MapF
import qualified Stubs.Translate.Intrinsic as STI

instance STC.TupleArch SAA.AArch32 ctx where

instance STC.StubsArch SAA.AArch32 where 
    type instance ArchTypeMatch SAA.AArch32 'SA.StubsInt = LCT.BVType (STC.ArchIntSize SAA.AArch32)
    type instance ArchTypeMatch SAA.AArch32 'SA.StubsUInt = LCT.BVType (STC.ArchIntSize SAA.AArch32)
    type instance ArchTypeMatch SAA.AArch32 'SA.StubsLong = LCT.BVType (STC.ArchLongSize SAA.AArch32)
    type instance ArchTypeMatch SAA.AArch32 'SA.StubsShort = LCT.BVType (STC.ArchShortSize SAA.AArch32)
    type instance ArchTypeMatch SAA.AArch32 'SA.StubsULong = LCT.BVType (STC.ArchLongSize SAA.AArch32)
    type instance ArchTypeMatch SAA.AArch32 'SA.StubsUShort = LCT.BVType (STC.ArchShortSize SAA.AArch32)
    type instance ArchTypeMatch SAA.AArch32 'SA.StubsBool = LCT.BoolType
    type instance ArchTypeMatch SAA.AArch32 'SA.StubsUnit = LCT.UnitType
    type instance ArchTypeMatch SAA.AArch32 ('SA.StubsAlias s) = STC.ArchTypeMatch SAA.AArch32 (SA.ResolveAlias s)
    type instance ArchTypeMatch SAA.AArch32 ('SA.StubsIntrinsic s) = SA.ResolveIntrinsic s
    type instance ArchTypeMatch SAA.AArch32 ('SA.StubsTuple c) = LCT.StructType (STC.ArchTypeMatchCtx SAA.AArch32 c)

    type instance ArchIntSize SAA.AArch32 = 32
    type instance ArchShortSize SAA.AArch32 =16
    type instance ArchLongSize SAA.AArch32 = 64
    
    toCrucibleTy tyrepr = do
        case tyrepr of
            SA.StubsIntRepr -> return $ LCT.BVRepr (PN.knownNat @32)
            SA.StubsBoolRepr -> return LCT.BoolRepr
            SA.StubsUnitRepr -> return LCT.UnitRepr
            SA.StubsUIntRepr -> return $ LCT.BVRepr (PN.knownNat @32)
            SA.StubsLongRepr -> return $ LCT.BVRepr (PN.knownNat @64)
            SA.StubsShortRepr -> return $ LCT.BVRepr (PN.knownNat @16)
            SA.StubsULongRepr -> return $ LCT.BVRepr (PN.knownNat @64)
            SA.StubsUShortRepr -> return $ LCT.BVRepr (PN.knownNat @16)
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

    translateLit lit = do 
        let n = PN.knownNat @32
        let ln = PN.knownNat @64
        let sn = PN.knownNat @16
        case lit of 
            SA.BoolLit b -> LCCR.App $ LCCE.BoolLit b
            SA.UnitLit -> LCCR.App LCCE.EmptyApp
            SA.IntLit i -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit i)
            SA.LongLit i -> LCCR.App (LCCE.IntegerToBV ln $ LCCR.App $ LCCE.IntLit i)
            SA.ShortLit i -> LCCR.App (LCCE.IntegerToBV sn $ LCCR.App $ LCCE.IntLit i)
            SA.ULongLit u -> LCCR.App (LCCE.IntegerToBV ln $ LCCR.App $ LCCE.IntLit (naturalToInteger u))
            SA.UShortLit u -> LCCR.App (LCCE.IntegerToBV sn $ LCCR.App $ LCCE.IntLit (naturalToInteger u))
            SA.UIntLit u -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit (naturalToInteger u))


instance SPR.Preamble SAA.AArch32 where
    preambleMap SA.StubsSignature{SA.sigFnName="plus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @SAA.AArch32 WI.bvAdd "plus"
    preambleMap SA.StubsSignature{SA.sigFnName="mult",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @SAA.AArch32 WI.bvMul "mult"
    preambleMap SA.StubsSignature{SA.sigFnName="minus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @SAA.AArch32 WI.bvSub "minus"
    preambleMap SA.StubsSignature{SA.sigFnName="gt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @SAA.AArch32 WI.bvSgt "gt"
    preambleMap SA.StubsSignature{SA.sigFnName="lt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @SAA.AArch32 WI.bvSlt "lt"
    preambleMap SA.StubsSignature{SA.sigFnName="eq",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @SAA.AArch32 WI.bvEq "eq"
    preambleMap SA.StubsSignature{SA.sigFnName="int",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUIntRepr), SA.sigFnRetTy=SA.StubsIntRepr} = bvIdOverride @SAA.AArch32 "int"
    preambleMap SA.StubsSignature{SA.sigFnName="uint",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr), SA.sigFnRetTy=SA.StubsUIntRepr} = bvIdOverride @SAA.AArch32 "uint"
    preambleMap SA.StubsSignature{SA.sigFnName="int_s",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsShortRepr), SA.sigFnRetTy=SA.StubsIntRepr} = bvExtendOverride @SAA.AArch32 "int_s" True
    preambleMap SA.StubsSignature{SA.sigFnName="long_i",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr), SA.sigFnRetTy=SA.StubsLongRepr} = bvExtendOverride @SAA.AArch32 "long_i" True
    preambleMap SA.StubsSignature{SA.sigFnName="short",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUShortRepr), SA.sigFnRetTy=SA.StubsShortRepr} = bvIdOverride @SAA.AArch32 "short"
    preambleMap SA.StubsSignature{SA.sigFnName="ushort",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsShortRepr), SA.sigFnRetTy=SA.StubsUShortRepr} = bvIdOverride @SAA.AArch32 "ushort"
    preambleMap SA.StubsSignature{SA.sigFnName="long",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsULongRepr), SA.sigFnRetTy=SA.StubsLongRepr} = bvIdOverride @SAA.AArch32 "long"
    preambleMap SA.StubsSignature{SA.sigFnName="ulong",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsLongRepr), SA.sigFnRetTy=SA.StubsULongRepr} = bvIdOverride @SAA.AArch32 "ulong"
    preambleMap SA.StubsSignature{SA.sigFnName="uint_s",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUShortRepr), SA.sigFnRetTy=SA.StubsUIntRepr} = bvExtendOverride @SAA.AArch32 "uint_s" False 
    preambleMap SA.StubsSignature{SA.sigFnName="ulong_i",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUIntRepr), SA.sigFnRetTy=SA.StubsULongRepr} = bvExtendOverride @SAA.AArch32 "ulong_i" False
    preambleMap sig = error ("Missing implementation for preamble function:"++SA.sigFnName sig)

instance STI.OverrideArch SAA.AArch32 where 
  buildOverrides = pure []
    