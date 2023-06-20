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

module Stubs.Translate.Core where 

import Stubs.AST
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

type family ArchTypeMatch (arch :: *) (stubType :: StubsType) = (crucType :: LCT.CrucibleType) where
    ArchTypeMatch arch 'StubsInt = LCT.BVType (DMC.ArchAddrWidth arch)
    ArchTypeMatch arch 'StubsBool = LCT.BoolType
    ArchTypeMatch arch 'StubsUnit = LCT.UnitType
    ArchTypeMatch arch ('StubsAlias a b) = ArchTypeMatch arch b

type family StubToCrucCtx (arch :: *) (stubTy :: Ctx StubsType) = (crucTy :: Ctx LCT.CrucibleType) where
    StubToCrucCtx arch 'EmptyCtx = 'EmptyCtx
    StubToCrucCtx arch (a ::> k) = StubToCrucCtx arch a ::> ArchTypeMatch arch k

data StubsState arch ret args s = forall ret2 . (ret ~ ArchTypeMatch arch ret2) => StubsState {
    -- Environment with arch info 
    stStubsenv::StubsEnv arch,
    -- Return type of the current function being translated
    stRetRepr::StubsTypeRepr ret2,
    -- Map of variables in scope to registers
    stRegMap::MapF.MapF StubsVar (StubReg arch s), --TODO: this will have dynamic scoping if left as is
    -- Cache of expressions already made into atoms
    stAtomCache::MapF.MapF StubsExpr (StubAtom arch s),
    -- Parameter Atoms 
    stParams :: Ctx.Assignment (StubAtom arch s) args,
    -- Functions defined in program
    stFns :: Map.Map String (SomeHandle arch)
}

withReturn :: (forall ret2 . ret ~ ArchTypeMatch arch ret2 =>  StubsTypeRepr ret2 -> StubsM arch s args ret a ) -> StubsM arch s args ret a 
withReturn f = do 
    StubsState _ retrepr _ _ _ _ <- get
    f retrepr

data StubsEnv arch = StubsEnv {
    stArchWidth::PN.NatRepr (DMC.ArchAddrWidth arch)
}

type StubsM arch s args ret a= (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => LCCG.Generator (DMS.MacawExt arch) s (StubsState arch ret args) ret IO a

class Monad m => HasStubsEnv arch m | m -> arch where
    getStubEnv :: m (StubsEnv arch)

instance HasStubsEnv arch (ReaderT (StubsEnv arch) IO) where
    getStubEnv = ask

data StubReg arch s (a::StubsType) = forall tp. (tp ~ ArchTypeMatch arch a) => StubReg (LCCR.Reg s tp) (StubsTypeRepr a)
data StubAtom arch s (a::StubsType) = forall tp . (tp ~ ArchTypeMatch arch a) => StubAtom (LCCR.Atom s tp) (StubsTypeRepr a)

data StubHandle arch (a::Ctx StubsType) (r::StubsType) = forall args ret . (args ~ StubToCrucCtx arch a, ret ~ ArchTypeMatch arch r) => StubHandle (Ctx.Assignment StubsTypeRepr a) (StubsTypeRepr r) (LCF.FnHandle args ret)

data SomeHandle arch = forall a b . SomeHandle (StubHandle arch a b)