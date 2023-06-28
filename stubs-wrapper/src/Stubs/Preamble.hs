{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Stubs.Preamble where

import qualified Data.Macaw.Symbolic as DMS
import qualified What4.Interface as WI
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.Simulator as LCS
import qualified Stubs.AST as SA
import qualified Stubs.Translate.Core as STC

class (DMS.SymArchConstraints arch) => Preamble arch where 
    preambleMap :: (bak ~ LCBO.OnlineBackend solver scope st fs,WI.IsExprBuilder sym, LCB.HasSymInterface sym bak) => 
               SA.StubsSignature args ret -> 
               (bak -> LCS.Override p sym ext (STC.ArchTypeMatchCtx arch args) (STC.ArchTypeMatch arch ret)) 

stubsPreamble :: [SA.SomeStubsSignature]
stubsPreamble = [
    SA.SomeStubsSignature(SA.StubsSignature "plus" (Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) SA.StubsIntRepr),
    SA.SomeStubsSignature(SA.StubsSignature "minus" (Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) SA.StubsIntRepr),
    SA.SomeStubsSignature(SA.StubsSignature "mult" (Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) SA.StubsIntRepr),
    SA.SomeStubsSignature(SA.StubsSignature "gt" (Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) SA.StubsBoolRepr),
    SA.SomeStubsSignature(SA.StubsSignature "lt" (Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) SA.StubsBoolRepr),
    SA.SomeStubsSignature(SA.StubsSignature "eq" (Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) SA.StubsBoolRepr),
    SA.SomeStubsSignature(SA.StubsSignature "int" (Ctx.extend Ctx.empty SA.StubsUIntRepr) SA.StubsIntRepr),
    SA.SomeStubsSignature(SA.StubsSignature "uint" (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsUIntRepr)
    ]

