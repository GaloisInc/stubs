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
import qualified Data.Macaw.Symbolic as DMS

import qualified Lang.Crucible.CFG.Generator as LCCG
import qualified Lang.Crucible.CFG.Expr as LCCE
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.RWS

type family ArchTypeMatch (arch :: *) (stubType :: StubsType) = (crucType :: LCT.CrucibleType) where
    ArchTypeMatch arch 'StubsInt = LCT.BVType (DMC.ArchAddrWidth arch)
    ArchTypeMatch arch 'StubsBool = LCT.BoolType
    ArchTypeMatch arch 'StubsUnit = LCT.UnitType
    ArchTypeMatch arch ('StubsAlias a b) = ArchTypeMatch arch b

type family StubToCrucCtx (arch :: *) (stubTy :: Ctx StubsType) = (crucTy :: Ctx LCT.CrucibleType) where
    StubToCrucCtx arch 'EmptyCtx = 'EmptyCtx
    StubToCrucCtx arch (a ::> k) = StubToCrucCtx arch a ::> ArchTypeMatch arch k

data StubsState arch ret s = forall ret2 . (ret ~ ArchTypeMatch arch ret2) => StubsState {
    stStubsenv::StubsEnv arch,
    stRetRepr::StubsTypeRepr ret2
}
data StubsEnv arch = StubsEnv {
    stArchWidth::PN.NatRepr (DMC.ArchAddrWidth arch)
}

type StubsM arch s ret a = (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => LCCG.Generator (DMS.MacawExt arch) s (StubsState arch ret) ret IO a

class Monad m => HasStubsEnv arch m | m -> arch where
    getStubEnv :: m (StubsEnv arch)

instance HasStubsEnv arch (Reader (StubsEnv arch)) where
    getStubEnv = ask

asStubsEnv :: Monad m' => (forall m. HasStubsEnv arch m => m a) ->  LCCG.Generator ext s (StubsState arch ret) ret m' a
asStubsEnv f = do
    v <- gets stStubsenv
    return $ runReader f v
