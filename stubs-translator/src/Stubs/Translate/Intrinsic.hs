{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

{-|
Description: Override Module definitions to allow for working with 'Intrinsic' types such as pointers

This module contains the definitions for Override Modules, which allow Crucible level overrides to be written, and exposed via Intrinsic Types.
This allows for more complex concepts like memory to be written directly in Haskell, and exposed to Stubs-level programs.
-}

module Stubs.Translate.Intrinsic where 
import qualified Stubs.AST as SA
import qualified Stubs.Translate.Core as STC
import qualified Lang.Crucible.Simulator as LCS
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Parameterized as P
import qualified Lang.Crucible.Types as LCT
import qualified Data.Parameterized.Context as Ctx

-- | Declaration of an Intrinsic type. These are similar to Opaques, but map directly into a Crucible type instead of a Stubs type
data IntrinsicTyDecl s tp = IntrinsicTyDecl (P.SymbolRepr s) (LCT.TypeRepr tp)
data SomeIntrinsicTyDecl = forall s tp . SomeIntrinsicTyDecl (IntrinsicTyDecl s tp)

-- | A Module consisting of Haskell Overrides rather than Stubs-level functions
data OverrideModule arch = OverrideModule {
    ovModuleName :: String, 
    ovDecls :: [SomeStubsOverride arch],
    ovTyDecls :: [SomeIntrinsicTyDecl],
    ovInits :: [String] --init fns
}

data StubsOverride arch (args:: LCT.Ctx SA.StubsType) (ret::SA.StubsType) (cargs:: LCT.Ctx LCT.CrucibleType) (cret::LCT.CrucibleType) = (STC.StubsArch arch) =>StubsOverride (forall sym p . STC.Sym sym -> LCS.Override p sym (DMS.MacawExt arch) cargs cret) (Ctx.Assignment LCT.TypeRepr cargs) (LCT.TypeRepr cret)

-- | An Override and a matching Signature, needed for type checking
data SomeStubsOverride arch = forall args ret cargs cret. (STC.StubsArch arch) => SomeStubsOverride (StubsOverride arch args ret cargs cret) (SA.StubsSignature args ret)
