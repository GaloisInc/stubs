{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Stubs.Preamble.AArch32() where
import qualified Stubs.AST as SA
import qualified What4.Interface as WI
import qualified Stubs.Preamble as SPR
import qualified Data.Parameterized.Context as Ctx
import Data.Macaw.X86.ArchTypes ()
import Data.Macaw.X86.Symbolic ()
import qualified SemMC.Architecture.AArch32 as SAA
import Data.Macaw.AArch32.Symbolic ()
import Stubs.Preamble.Common

instance SPR.Preamble SAA.AArch32 where
    preambleMap SA.StubsSignature{SA.sigFnName="plus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @SAA.AArch32 WI.bvAdd "plus"
    preambleMap SA.StubsSignature{SA.sigFnName="mult",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @SAA.AArch32 WI.bvMul "mult"
    preambleMap SA.StubsSignature{SA.sigFnName="minus",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsIntRepr} = arithBinOverride @SAA.AArch32 WI.bvSub "minus"
    preambleMap SA.StubsSignature{SA.sigFnName="gt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @SAA.AArch32 WI.bvSgt "gt"
    preambleMap SA.StubsSignature{SA.sigFnName="lt",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @SAA.AArch32 WI.bvSlt "lt"
    preambleMap SA.StubsSignature{SA.sigFnName="eq",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr Ctx.:> SA.StubsIntRepr ), SA.sigFnRetTy=SA.StubsBoolRepr} = cmpBinOverride @SAA.AArch32 WI.bvEq "eq"
    preambleMap SA.StubsSignature{SA.sigFnName="int",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsUIntRepr), SA.sigFnRetTy=SA.StubsIntRepr} = bvIdOverride @SAA.AArch32 "int"
    preambleMap SA.StubsSignature{SA.sigFnName="Uint",SA.sigFnArgTys=(Ctx.Empty Ctx.:> SA.StubsIntRepr), SA.sigFnRetTy=SA.StubsUIntRepr} = bvIdOverride @SAA.AArch32 "uint"
    preambleMap sig = error ("Missing implementation for preamble function:"++SA.sigFnName sig)
