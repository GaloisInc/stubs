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

module Stubs.Translate.Type (toCrucibleTy, toCrucibleTyCtx) where

import Stubs.AST
import Stubs.Translate.Core
import qualified Lang.Crucible.Types as LCT

import Data.Parameterized.Context as Ctx
import qualified Stubs.Translate.Core as STC

toCrucibleTyCtx :: forall ctx arch m. (STC.StubsArch arch, HasStubsEnv arch m) => Ctx.Assignment StubsTypeRepr ctx -> m (Ctx.Assignment LCT.TypeRepr (ArchTypeMatchCtx arch ctx))
toCrucibleTyCtx assign = case alist of
        AssignEmpty -> return Ctx.empty
        AssignExtend a b -> do
            bc <- toCrucibleTy b
            ac <- toCrucibleTyCtx a
            return $ Ctx.extend ac bc
    where
        alist = Ctx.viewAssign assign