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
    SA.SomeStubsSignature(SA.StubsSignature "uint" (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsUIntRepr),
    SA.SomeStubsSignature(SA.StubsSignature "long" (Ctx.extend Ctx.empty SA.StubsULongRepr) SA.StubsLongRepr),
    SA.SomeStubsSignature(SA.StubsSignature "ulong" (Ctx.extend Ctx.empty SA.StubsLongRepr) SA.StubsULongRepr),
    SA.SomeStubsSignature(SA.StubsSignature "short" (Ctx.extend Ctx.empty SA.StubsUShortRepr) SA.StubsShortRepr),
    SA.SomeStubsSignature(SA.StubsSignature "ushort" (Ctx.extend Ctx.empty SA.StubsShortRepr) SA.StubsUShortRepr),
    SA.SomeStubsSignature(SA.StubsSignature "long_i" (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsLongRepr),
    SA.SomeStubsSignature(SA.StubsSignature "int_s" (Ctx.extend Ctx.empty SA.StubsShortRepr) SA.StubsIntRepr),
    SA.SomeStubsSignature(SA.StubsSignature "ulong_i" (Ctx.extend Ctx.empty SA.StubsUIntRepr) SA.StubsULongRepr),
    SA.SomeStubsSignature(SA.StubsSignature "uint_s" (Ctx.extend Ctx.empty SA.StubsUShortRepr) SA.StubsUIntRepr)
    ]

