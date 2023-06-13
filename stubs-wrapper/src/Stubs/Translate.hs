{-#LANGUAGE GADTs #-}
{-#LANGUAGE DataKinds #-}
{-#LANGUAGE KindSignatures #-}
{-#LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes#-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Stubs.Translate where

import Stubs.AST
import Stubs.Translate.Core
import Stubs.Translate.Type
import qualified Data.Macaw.CFG as DMC
import Data.Parameterized.Some
import Data.Parameterized.Nonce
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Macaw.Symbolic as DMS

import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.CFG.Generator as LCCG
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.CFG.Expr as LCCE
import qualified What4.FunctionName as WF
import qualified What4.ProgramLoc as WF
import qualified Data.Text as T

import Control.Monad.RWS
import Control.Monad.Reader (runReader)
import Lang.Crucible.CFG.Core (StringInfoRepr(UnicodeRepr))
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Data.Map as Map

translateExpr :: forall arch s ret b sret. (b ~ ArchTypeMatch arch sret) => StubsExpr sret -> StubsM arch s ret (LCCR.Expr (DMS.MacawExt arch) s b)
translateExpr e = do
    let n = DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)
    return $ case e of
        BoolLit b -> LCCR.App $ LCCE.BoolLit b
        UnitLit -> LCCR.App LCCE.EmptyApp
        IntLit i -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit i)

translateStmt :: forall arch s ret . StubsStmt  -> StubsM arch s (ArchTypeMatch arch ret) (LCCR.Expr (DMS.MacawExt arch) s (ArchTypeMatch arch ret))
translateStmt stmt = do
    StubsState _ retty <- get
    case stmt of
        Return e -> do
            case PN.testEquality (stubsExprToTy e) retty of
                Just PN.Refl -> do
                    ce <- translateExpr e
                    LCCG.returnFromFunction ce
                Nothing -> do
                    LCCG.reportError $  LCCR.App $ LCCE.StringEmpty UnicodeRepr
        --Assignment v e -> translateExpr e >>= (\ce -> return . LCCG.returnFromFunction ce)

translateStmts :: forall arch s ret . [StubsStmt] -> StubsM arch s (ArchTypeMatch arch ret) ()
translateStmts [] = return ()
translateStmts (s:stmts) = do
    _ <- translateStmt @_ @_ @ret s
    translateStmts @_ @_ @ret stmts

translateFn :: forall args ret sy arch . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => NonceGenerator IO sy -> LCF.HandleAllocator -> StubsFunction args ret ->  IO (LCSC.ParsedProgram (DMS.MacawExt arch))
translateFn ng hAlloc StubsFunction{stubFnName=name, stubFnArgTys=argtys, stubFnBody=body, stubFnRetTy=retty}= do
    let e = StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch))
    let args = runReader (stubToCrucTy argtys) e
    let cret = runReader (toCrucibleTy retty) e
    handle <- LCF.mkHandle' hAlloc (WF.functionNameFromText (T.pack name)) args cret
    (LCCR.SomeCFG q, aux) <- liftIO $ LCCG.defineFunction WF.InternalPos (Some ng) handle $ const (StubsState{stStubsenv=e,stRetRepr=retty},  translateStmts @arch @_ @ret body >> LCCG.reportError (LCCR.App $ LCCE.StringEmpty UnicodeRepr))
    let t = LCSC.ParsedProgram {
        LCSC.parsedProgGlobals = Map.empty,
        LCSC.parsedProgExterns = Map.empty,
        LCSC.parsedProgCFGs = [LCSC.ACFG args cret q],
        LCSC.parsedProgForwardDecs = Map.empty
    }
    return t

translateDecls :: forall arch s . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => NonceGenerator IO s -> LCF.HandleAllocator -> [SomeStubsFunction] -> IO [LCSC.ParsedProgram (DMS.MacawExt arch)]
translateDecls ng hAlloc fns = do
    case fns of
        [] -> return []
        ((SomeStubsFunction f):frest) -> do
            prog <- translateFn @_ @_ @_ @arch ng hAlloc f
            cfrest <- translateDecls ng hAlloc frest
            return $ prog:cfrest