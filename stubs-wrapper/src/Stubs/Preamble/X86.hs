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
module Stubs.Preamble.X86() where
import qualified Stubs.AST as SA
import qualified Data.Macaw.X86 as DMX
import qualified What4.Interface as WI
import qualified Stubs.Preamble as SPR
import qualified Data.Parameterized.Context as Ctx
import Data.Macaw.X86.ArchTypes ()
import Data.Macaw.X86.Symbolic ()
import Stubs.Preamble.Common 
import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Types as LCT
import qualified Stubs.Translate.Core as STC
import qualified Data.Parameterized.NatRepr as PN
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.CFG.Expr as LCCE
import GHC.Natural (naturalToInteger)

instance STC.StubsArch DMX.X86_64 where 
    type instance ArchTypeMatch DMX.X86_64 'SA.StubsInt = LCT.BVType (STC.ArchIntSize DMX.X86_64)
    type instance ArchTypeMatch DMX.X86_64 'SA.StubsUInt = LCT.BVType (STC.ArchIntSize DMX.X86_64)
    type instance ArchTypeMatch DMX.X86_64 'SA.StubsLong = LCT.BVType (STC.ArchLongSize DMX.X86_64)
    type instance ArchTypeMatch DMX.X86_64 'SA.StubsShort = LCT.BVType (STC.ArchShortSize DMX.X86_64)
    type instance ArchTypeMatch DMX.X86_64 'SA.StubsBool = LCT.BoolType
    type instance ArchTypeMatch DMX.X86_64 'SA.StubsUnit = LCT.UnitType
    type instance ArchTypeMatch DMX.X86_64 ('SA.StubsAlias a b) = STC.ArchTypeMatch DMX.X86_64 b

    type instance ArchIntSize DMX.X86_64 = 32
    type instance ArchShortSize DMX.X86_64 = 16
    type instance ArchLongSize DMX.X86_64 = 64
    
    toCrucibleTy tyrepr = do
        case tyrepr of
            SA.StubsIntRepr -> return $ LCT.BVRepr (PN.knownNat @32)
            SA.StubsBoolRepr -> return LCT.BoolRepr
            SA.StubsUnitRepr -> return LCT.UnitRepr
            SA.StubsAliasRepr _ t -> STC.toCrucibleTy $ STC.resolveAlias t
            SA.StubsUIntRepr -> return $ LCT.BVRepr (PN.knownNat @32)
            SA.StubsLongRepr -> return $ LCT.BVRepr (PN.knownNat @64)
            SA.StubsShortRepr-> return $ LCT.BVRepr (PN.knownNat @16)

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
    preambleMap sig = error ("Missing implementation for preamble function:"++SA.sigFnName sig)