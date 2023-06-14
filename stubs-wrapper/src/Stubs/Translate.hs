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

module Stubs.Translate (
 translateExpr,
 translateDecls,
 translateFn,
 translateStmt,
 translateStmts
) where

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
import qualified Data.Parameterized.Map as MapF
import qualified Data.Map as Map
import qualified Stubs.AST as SA

--Unexported Internal Function
translateExpr'' :: forall arch s ret b sret ext. (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext) => SA.StubsExpr sret -> StubsM arch s ret (LCCR.Expr (DMS.MacawExt arch) s b)
translateExpr'' e = do
    let n = DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)
    return $ case e of
        SA.BoolLit b -> LCCR.App $ LCCE.BoolLit b
        SA.UnitLit -> LCCR.App LCCE.EmptyApp
        SA.IntLit i -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit i)
        SA.VarLit _ -> error "internal translateExpr called on VarLit"

-- Unexported Internal Function
translateExpr' :: forall arch s ret b sret. (b ~ ArchTypeMatch arch sret, LCCE.IsSyntaxExtension(DMS.MacawExt arch)) => SA.StubsExpr sret -> StubsM arch s ret (LCCR.Atom s b)
translateExpr' e = do
    StubsState _ _ regMap _<- get
    case e of 
        SA.VarLit v -> case MapF.lookup v regMap of 
            Just (StubReg reg _) -> do 
                t <- LCCG.readReg reg
                LCCG.mkAtom t
            Nothing -> error "Undefined VarLit encountered"
        _ -> do 
            ce <- translateExpr'' e 
            LCCG.mkAtom ce

translateExpr  :: forall arch s ret b sret ext. (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext) => SA.StubsExpr sret -> StubsM arch s ret (LCCR.Expr (DMS.MacawExt arch) s b)
translateExpr e = do 
    StubsState env retty regMap cache <- get
    case MapF.lookup e cache of 
        Nothing -> do 
            t <- translateExpr' e 
            _ <- put (StubsState env retty regMap $ MapF.insert e (StubAtom t) cache )
            return $ LCCG.AtomExpr t
        Just (StubAtom t) -> return $ LCCG.AtomExpr t

translateStmt :: forall arch s ret . SA.StubsStmt  -> StubsM arch s (ArchTypeMatch arch ret) ()
translateStmt stmt = do
    StubsState a retty regMap cache <- get
    case stmt of
        SA.Return e -> do
            case PN.testEquality (SA.stubsExprToTy e) retty of
                Just PN.Refl -> do
                    ce <- translateExpr e
                    LCCG.returnFromFunction ce
                Nothing -> do
                    LCCG.reportError $  LCCR.App $ LCCE.StringEmpty UnicodeRepr
        SA.Assignment v e -> do
            ce <- translateExpr e
            case MapF.lookup v regMap of -- Is v in scope already?
                Nothing -> do
                        reg <- LCCG.newReg ce
                        _ <- put (StubsState a retty (MapF.insert v (StubReg reg (SA.varType v)) regMap) cache)
                        return ()
                Just (StubReg reg _) -> do
                    _ <- LCCG.assignReg reg ce
                    return ()
        SA.ITE c t e -> do
            cond <- translateExpr c
            LCCG.ifte_ cond (translateStmts @_ @_ @ret t) (translateStmts @_ @_ @ret e)
        SA.Loop c body -> do
            LCCG.while (WF.InternalPos, translateExpr c ) (WF.InternalPos, translateStmts @_ @_ @ret body)

translateStmts :: forall arch s ret . [SA.StubsStmt] -> StubsM arch s (ArchTypeMatch arch ret) ()
translateStmts [] = return ()
translateStmts (s:stmts) = do
    _ <- translateStmt @_ @_ @ret s
    translateStmts @_ @_ @ret stmts

translateFn :: forall args ret sy arch . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => NonceGenerator IO sy -> LCF.HandleAllocator -> SA.StubsFunction args ret ->  IO (LCSC.ACFG (DMS.MacawExt arch))
translateFn ng hAlloc SA.StubsFunction{SA.stubFnName=name, SA.stubFnArgTys=argtys, SA.stubFnBody=body, SA.stubFnRetTy=retty}= do
    let e = StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch))
    let args = runReader (stubToCrucTy argtys) e
    let cret = runReader (toCrucibleTy retty) e
    handle <- LCF.mkHandle' hAlloc (WF.functionNameFromText (T.pack name)) args cret
    (LCCR.SomeCFG q, aux) <- liftIO $ LCCG.defineFunction WF.InternalPos (Some ng) handle $ const (StubsState{stStubsenv=e,stRetRepr=retty,stRegMap=MapF.empty,stAtomCache=MapF.empty},  translateStmts @arch @_ @ret body >> LCCG.reportError (LCCR.App $ LCCE.StringEmpty UnicodeRepr))
    let t = LCSC.ACFG args cret q
    return t

translateDecls :: forall arch s . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => NonceGenerator IO s -> LCF.HandleAllocator -> [SA.SomeStubsFunction] -> IO (LCSC.ParsedProgram (DMS.MacawExt arch))
translateDecls ng hAlloc fns = do
    r <- mapM (\(SA.SomeStubsFunction f) -> translateFn @_ @_ @_ @arch ng hAlloc f) fns
    return $ LCSC.ParsedProgram {
        LCSC.parsedProgGlobals = Map.empty,
        LCSC.parsedProgExterns = Map.empty,
        LCSC.parsedProgCFGs = r,
        LCSC.parsedProgForwardDecs = Map.empty
    }