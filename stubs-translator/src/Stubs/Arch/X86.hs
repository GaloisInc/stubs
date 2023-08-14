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
Description: Preamble Instance for X86_64
-}
module Stubs.Arch.X86() where
import qualified Stubs.AST as SA
import qualified Data.Macaw.X86 as DMX
import qualified What4.Interface as WI
import qualified Stubs.Preamble as SPR
import qualified Data.Parameterized.Context as Ctx
import Data.Macaw.X86.ArchTypes ()
import Data.Macaw.X86.Symbolic ()
import Stubs.Preamble.Common( arithBinOverride, cmpBinOverride, bvIdOverride, bvExtendOverride )
import qualified Lang.Crucible.Types as LCT
import qualified Stubs.Translate.Core as STC
import qualified Data.Parameterized.NatRepr as PN
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.CFG.Expr as LCCE
import GHC.Natural (naturalToInteger)
import qualified Data.Parameterized.Map as MapF
import qualified Stubs.Translate.Intrinsic as STI
import qualified Data.Parameterized as P
import qualified Stubs.Common as SC 
import qualified Lang.Crucible.Simulator as LCS
import Control.Monad.IO.Class (MonadIO)

instance STC.StubsArch DMX.X86_64 where

    type instance ArchIntSize DMX.X86_64 = 32
    type instance ArchShortSize DMX.X86_64 = 16
    type instance ArchLongSize DMX.X86_64 = 64

    toCrucibleTy tyrepr = do
        case tyrepr of
            SA.StubsIntRepr -> return $ LCT.BVRepr (PN.knownNat @32)
            SA.StubsBoolRepr -> return LCT.BoolRepr
            SA.StubsUnitRepr -> return LCT.UnitRepr
            SA.StubsUIntRepr -> return $ LCT.BVRepr (PN.knownNat @32)
            SA.StubsLongRepr -> return $ LCT.BVRepr (PN.knownNat @64)
            SA.StubsShortRepr-> return $ LCT.BVRepr (PN.knownNat @16)
            SA.StubsULongRepr -> return $ LCT.BVRepr (PN.knownNat @64)
            SA.StubsUShortRepr-> return $ LCT.BVRepr (PN.knownNat @16)
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
                internal <- STC.toCrucibleTyCtx @_ @DMX.X86_64 t
                return (LCT.StructRepr internal)

    translateLit lit = do
        let n = PN.knownNat @32
        let ln = PN.knownNat @64
        let sn = PN.knownNat @16
        case lit of
            SA.BoolLit b -> LCCR.App $ LCCE.BoolLit b
            SA.UnitLit -> LCCR.App LCCE.EmptyApp
            SA.IntLit i -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit i)
            SA.LongLit i -> LCCR.App (LCCE.IntegerToBV ln $ LCCR.App $ LCCE.IntLit i)
            SA.UIntLit u -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit (naturalToInteger u))
            SA.ULongLit u -> LCCR.App (LCCE.IntegerToBV ln $ LCCR.App $ LCCE.IntLit (naturalToInteger u))
            SA.UShortLit u -> LCCR.App (LCCE.IntegerToBV sn $ LCCR.App $ LCCE.IntLit (naturalToInteger u))
            SA.ShortLit s -> LCCR.App (LCCE.IntegerToBV sn $ LCCR.App $ LCCE.IntLit s)

instance SPR.Preamble DMX.X86_64 where
    preambleMap SA.StubsSignature{SA.sigFnName="plus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @DMX.X86_64 WI.bvAdd "plus"
    preambleMap SA.StubsSignature{SA.sigFnName="mult",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @DMX.X86_64 WI.bvMul "mult"
    preambleMap SA.StubsSignature{SA.sigFnName="minus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @DMX.X86_64 WI.bvSub "minus"
    preambleMap SA.StubsSignature{SA.sigFnName="gt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @DMX.X86_64 WI.bvSgt "gt"
    preambleMap SA.StubsSignature{SA.sigFnName="lt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @DMX.X86_64 WI.bvSlt "lt"
    preambleMap SA.StubsSignature{SA.sigFnName="eq",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @DMX.X86_64 WI.bvEq "eq"
    preambleMap SA.StubsSignature{SA.sigFnName="int",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUIntRepr), SA.sigFnRetTy=SA.StubsIntRepr} = bvIdOverride @DMX.X86_64 "int"
    preambleMap SA.StubsSignature{SA.sigFnName="uint",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr), SA.sigFnRetTy=SA.StubsUIntRepr} = bvIdOverride @DMX.X86_64 "uint"
    preambleMap SA.StubsSignature{SA.sigFnName="int_s",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsShortRepr), SA.sigFnRetTy=SA.StubsIntRepr} = bvExtendOverride @DMX.X86_64 "int_s" True
    preambleMap SA.StubsSignature{SA.sigFnName="long_i",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr), SA.sigFnRetTy=SA.StubsLongRepr} = bvExtendOverride @DMX.X86_64 "long_i" True
    preambleMap SA.StubsSignature{SA.sigFnName="short",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUShortRepr), SA.sigFnRetTy=SA.StubsShortRepr} = bvIdOverride @DMX.X86_64 "short"
    preambleMap SA.StubsSignature{SA.sigFnName="ushort",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsShortRepr), SA.sigFnRetTy=SA.StubsUShortRepr} = bvIdOverride @DMX.X86_64 "ushort"
    preambleMap SA.StubsSignature{SA.sigFnName="long",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsULongRepr), SA.sigFnRetTy=SA.StubsLongRepr} = bvIdOverride @DMX.X86_64 "long"
    preambleMap SA.StubsSignature{SA.sigFnName="ulong",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsLongRepr), SA.sigFnRetTy=SA.StubsULongRepr} = bvIdOverride @DMX.X86_64 "ulong"
    preambleMap SA.StubsSignature{SA.sigFnName="uint_s",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUShortRepr), SA.sigFnRetTy=SA.StubsUIntRepr} = bvExtendOverride @DMX.X86_64 "uint_s" False
    preambleMap SA.StubsSignature{SA.sigFnName="ulong_i",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUIntRepr), SA.sigFnRetTy=SA.StubsULongRepr} = bvExtendOverride @DMX.X86_64 "ulong_i" False

    preambleMap sig = error ("Missing implementation for preamble function:"++SA.sigFnName sig)

instance STI.OverrideArch DMX.X86_64 where
     buildOverrides = do 
        allocModule <- mallocOv @DMX.X86_64
        return [allocModule]


mallocStub :: (STC.StubsArch arch) => P.SymbolRepr s -> STI.SomeStubsOverride arch
mallocStub ptr = STI.SomeStubsOverride (STI.StubsOverride (\(SC.Sym sym _)-> do
          LCS.mkOverride' "malloc" LCT.BoolRepr (do
              LCS.RegMap (Ctx.Empty Ctx.:> _) <-  LCS.getOverrideArgs
              return $ WI.truePred sym
            )) (Ctx.extend Ctx.empty (LCT.BVRepr @32 WI.knownRepr)) LCT.BoolRepr) (SA.StubsSignature "malloc" (Ctx.extend Ctx.empty SA.StubsIntRepr) (SA.StubsIntrinsicRepr ptr))

mallocOv :: (STC.StubsArch arch, MonadIO m) => m (STI.OverrideModule arch)
mallocOv = do 
    P.Some ptr <- return $ P.someSymbol "Pointer"
    return $ STI.OverrideModule "alloc" [mallocStub ptr] [STI.SomeIntrinsicTyDecl (STI.IntrinsicTyDecl ptr LCT.BoolRepr)] []