{-#LANGUAGE GADTs #-}
{-#LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes#-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}

module Stubs.Translate.Core where

import qualified Lang.Crucible.Types as LCT
import qualified Data.Macaw.CFG as DMC

import qualified Data.Parameterized.NatRepr as PN
import Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Map as Map
import qualified Data.Macaw.Symbolic as DMS

import qualified Lang.Crucible.CFG.Generator as LCCG
import qualified Lang.Crucible.CFG.Expr as LCCE
import qualified Lang.Crucible.CFG.Reg as LCCR
import Control.Monad.RWS
import Control.Monad.Reader (ReaderT)
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Stubs.AST as SA
import GHC.TypeNats (Nat, KnownNat)
import qualified Data.Parameterized as P
import Unsafe.Coerce (unsafeCoerce)


type family ArchTypeMatchCtx (arch :: *) (stubTy :: Ctx SA.StubsType) = (crucTy :: Ctx LCT.CrucibleType) where
    ArchTypeMatchCtx arch 'EmptyCtx = 'EmptyCtx
    ArchTypeMatchCtx arch (a ::> k) = ArchTypeMatchCtx arch a ::> ArchTypeMatch arch k


class (DMS.SymArchConstraints arch, 
        ArchTypeMatch arch SA.StubsBool ~ LCT.BoolType, 
        16 PN.<= ArchIntSize arch, 1 PN.<= ArchIntSize arch, KnownNat (ArchIntSize arch),
        16 PN.<= ArchShortSize arch, 1 PN.<= ArchShortSize arch, KnownNat (ArchShortSize arch),
        16 PN.<= ArchLongSize arch, 1 PN.<= ArchLongSize arch, KnownNat (ArchLongSize arch)) => StubsArch arch where 
    type ArchTypeMatch arch (stubType :: SA.StubsType) :: LCT.CrucibleType
    type ArchIntSize arch :: Nat
    type ArchShortSize arch :: Nat
    type ArchLongSize arch :: Nat 
    toCrucibleTy ::forall a m. (HasStubsEnv arch m) => SA.StubsTypeRepr a -> m (LCT.TypeRepr (ArchTypeMatch arch a))
    translateLit :: (b ~ ArchTypeMatch arch a) => SA.StubsLit a -> LCCR.Expr (DMS.MacawExt arch) s b


data StubsState arch ret args s = forall ret2 . (ret ~ ArchTypeMatch arch ret2) => StubsState {
    -- Environment with arch info 
    stStubsenv::StubsEnv arch,
    -- Return type of the current function being translated
    stRetRepr::SA.StubsTypeRepr ret2,
    -- Map of variables in scope to registers
    stRegMap::MapF.MapF SA.StubsVar (StubReg arch s), --TODO: this will have dynamic scoping if left as is
    -- Cache of expressions already made into atoms
    stAtomCache::MapF.MapF SA.StubsExpr (StubAtom arch s),
    -- Parameter Atoms 
    stParams :: Ctx.Assignment (StubAtom arch s) args,
    -- Functions defined in program
    stFns :: Map.Map String (SomeHandle arch)
}

withReturn :: (forall ret2 . ret ~ ArchTypeMatch arch ret2 =>  SA.StubsTypeRepr ret2 -> StubsM arch s args ret a ) -> StubsM arch s args ret a
withReturn f = do
    StubsState _ retrepr _ _ _ _ <- get
    f retrepr

data WrappedStubsTypeAliasRepr (s :: P.Symbol) where
    WrappedStubsTypeAliasRepr :: P.SymbolRepr s -> SA.StubsTypeRepr (SA.ResolveAlias s) -> WrappedStubsTypeAliasRepr s 
    deriving Show 

instance P.ShowF WrappedStubsTypeAliasRepr where 
    showF (WrappedStubsTypeAliasRepr s t) = "WrappedAlias: " ++ show s ++ " " ++ show t

coerceToAlias :: P.SymbolRepr s -> SA.StubsTypeRepr a -> WrappedStubsTypeAliasRepr s
coerceToAlias s repr = WrappedStubsTypeAliasRepr s (unsafeCoerce repr)


data StubsEnv arch = StubsEnv {
    stArchWidth::PN.NatRepr (DMC.ArchAddrWidth arch)
    , stTyMap :: MapF.MapF P.SymbolRepr WrappedStubsTypeAliasRepr
}

type StubsM arch s args ret a= (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => LCCG.Generator (DMS.MacawExt arch) s (StubsState arch ret args) ret IO a

class (Monad m,MonadFail m) => HasStubsEnv arch m | m -> arch where
    getStubEnv :: m (StubsEnv arch)

instance HasStubsEnv arch (ReaderT (StubsEnv arch) IO) where
    getStubEnv = ask

instance HasStubsEnv arch (ReaderT (StubsEnv arch) (LCCG.Generator (DMS.MacawExt arch) s (StubsState arch ret args) ret IO) ) where
    getStubEnv = ask

data StubReg arch s (a::SA.StubsType) = forall tp. (tp ~ ArchTypeMatch arch a) => StubReg (LCCR.Reg s tp) (SA.StubsTypeRepr a)
data StubAtom arch s (a::SA.StubsType) = forall tp . (tp ~ ArchTypeMatch arch a) => StubAtom (LCCR.Atom s tp) (SA.StubsTypeRepr a)

data StubHandle arch (a::Ctx SA.StubsType) (r::SA.StubsType) = forall args ret . (args ~ ArchTypeMatchCtx arch a, ret ~ ArchTypeMatch arch r) => StubHandle (Ctx.Assignment SA.StubsTypeRepr a) (SA.StubsTypeRepr r) (LCF.FnHandle args ret)

data SomeHandle arch = forall a b . SomeHandle (StubHandle arch a b)