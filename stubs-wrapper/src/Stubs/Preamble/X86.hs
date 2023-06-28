{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Stubs.Preamble.X86() where
import qualified Stubs.AST as SA
import qualified Data.Macaw.X86 as DMX
import qualified What4.Interface as WI
import qualified Stubs.Preamble as SPR
import qualified Data.Parameterized.Context as Ctx
import Data.Macaw.X86.ArchTypes ()
import Data.Macaw.X86.Symbolic ()
import Stubs.Preamble.Common 

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