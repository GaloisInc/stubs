{-#LANGUAGE GADTs #-}
{-#LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes#-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Stubs.Translate.Type where

import Stubs.AST
import Stubs.Translate.Core
import qualified Lang.Crucible.Types as LCT

import Data.Parameterized.Context as Ctx
import qualified Data.Macaw.Symbolic as DMS


resolveAlias :: StubsTypeRepr a -> StubsTypeRepr a
resolveAlias (StubsAliasRepr _ a) = resolveAlias a
resolveAlias x = x

toCrucibleTy ::forall arch a m. (DMS.SymArchConstraints arch, HasStubsEnv arch m) => StubsTypeRepr a -> m (LCT.TypeRepr (ArchTypeMatch arch a))
toCrucibleTy tyrepr =
    case tyrepr of
        StubsIntRepr -> do
            n <- stArchWidth <$> getStubEnv
            return $ LCT.BVRepr n
        StubsBoolRepr -> return LCT.BoolRepr
        StubsUnitRepr -> return LCT.UnitRepr
        --StubsTupleRepr ctx -> Some $ LCT.UnitRepr -- todo change
        StubsAliasRepr _ t -> toCrucibleTy $ resolveAlias t


stubToCrucTy :: forall ctx arch m. (DMS.SymArchConstraints arch, HasStubsEnv arch m) => Ctx.Assignment StubsTypeRepr ctx -> m (Ctx.Assignment LCT.TypeRepr (StubToCrucCtx arch ctx))
stubToCrucTy assign = case alist of
        AssignEmpty -> return Ctx.empty
        AssignExtend a b -> do
            bc <- toCrucibleTy b
            ac <- stubToCrucTy a
            return $ Ctx.extend ac bc
    where
        alist = Ctx.viewAssign assign