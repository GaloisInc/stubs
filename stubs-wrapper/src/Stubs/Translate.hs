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
 translateStmts,
 translateProgram
) where

import Stubs.Translate.Core
import Stubs.Translate.Type
import qualified Data.Macaw.CFG as DMC
import Data.Parameterized.Some
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
import Control.Monad.Reader (ReaderT (runReaderT))
import Lang.Crucible.CFG.Core (StringInfoRepr(UnicodeRepr))
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Map as Map
import qualified Stubs.AST as SA
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Nonce as PN
import qualified Data.Parameterized as P

-- Unexported Internal Function
translateExpr' :: forall arch s ret b sret args . (b ~ ArchTypeMatch arch sret, LCCE.IsSyntaxExtension(DMS.MacawExt arch)) => SA.StubsExpr sret -> StubsM arch s ret (LCCR.Atom s b) args
translateExpr' e = do
    StubsState _ _ regMap _ argmap <- get
    case e of
        SA.VarLit v -> case MapF.lookup v regMap of
            Just (StubReg reg _) -> do
                t <- LCCG.readReg reg
                LCCG.mkAtom t
            Nothing -> error "Undefined VarLit encountered"
        SA.ArgLit (SA.StubsArg i ty) -> do
            case Ctx.intIndex i (Ctx.size argmap) of
                Nothing -> error "Argument index out of bounds"
                Just (Some idx) -> do
                    StubAtom a sty <- return $ argmap Ctx.! idx
                    Just P.Refl <- return $ P.testEquality ty sty
                    return a
        _ -> do
            ce <- translateExpr'' e
            LCCG.mkAtom ce
    where
        translateExpr'' :: forall ext. (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext) => SA.StubsExpr sret -> StubsM arch s ret (LCCR.Expr (DMS.MacawExt arch) s b) args
        translateExpr'' e' = do
            let n = DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)
            return $ case e' of
                SA.BoolLit b -> LCCR.App $ LCCE.BoolLit b
                SA.UnitLit -> LCCR.App LCCE.EmptyApp
                SA.IntLit i -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit i)
                SA.VarLit _ -> error "internal translateExpr called on VarLit"
                SA.ArgLit _ -> error "internal translateExpr called on ArgLit"

translateExpr  :: forall arch s ret b sret ext args . (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext) => SA.StubsExpr sret -> StubsM arch s ret (LCCR.Expr (DMS.MacawExt arch) s b) args
translateExpr e = do
    StubsState env retty regMap cache argmap <- get
    case MapF.lookup e cache of
        Nothing -> do
            t <- translateExpr' e
            _ <- put (StubsState env retty regMap (MapF.insert e (StubAtom t (SA.stubsExprToTy e)) cache) argmap)
            return $ LCCG.AtomExpr t
        Just (StubAtom t _) -> return $ LCCG.AtomExpr t

translateStmt :: forall arch s ret args . SA.StubsStmt  -> StubsM arch s (ArchTypeMatch arch ret) () args
translateStmt stmt = do
    StubsState a retty regMap cache argmap<- get
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
                        _ <- put (StubsState a retty (MapF.insert v (StubReg reg (SA.varType v)) regMap) cache argmap)
                        return ()
                Just (StubReg reg _) -> do
                    _ <- LCCG.assignReg reg ce
                    return ()
        SA.ITE c t e -> do
            cond <- translateExpr c
            LCCG.ifte_ cond (translateStmts @_ @_ @ret t) (translateStmts @_ @_ @ret e)
        SA.Loop c body -> do
            LCCG.while (WF.InternalPos, translateExpr c ) (WF.InternalPos, translateStmts @_ @_ @ret body)

translateStmts :: forall arch s ret args . [SA.StubsStmt] -> StubsM arch s (ArchTypeMatch arch ret) () args
translateStmts [] = return ()
translateStmts (s:stmts) = do
    _ <- translateStmt @_ @_ @ret s
    translateStmts @_ @_ @ret stmts

translateFn :: forall args ret s arch . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => PN.NonceGenerator IO s -> LCF.HandleAllocator -> SA.StubsFunction args ret ->  IO (LCSC.ACFG (DMS.MacawExt arch))
translateFn ng hAlloc SA.StubsFunction{SA.stubFnSig=SA.StubsSignature{SA.sigFnName=name, SA.sigFnArgTys=argtys, SA.sigFnRetTy=retty},SA.stubFnBody=body}= do
    let e = StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch))
    args <- runReaderT (stubToCrucTy argtys) e
    cret <- runReaderT (toCrucibleTy retty) e
    handle <- LCF.mkHandle' hAlloc (WF.functionNameFromText (T.pack name)) args cret
    (LCCR.SomeCFG q, aux) <- liftIO $ LCCG.defineFunction WF.InternalPos (Some ng) handle $ \crucArgs -> (StubsState e retty MapF.empty MapF.empty (translateFnArgs crucArgs argtys),
                                                                                                     translateStmts @arch @_ @ret body >> LCCG.reportError (LCCR.App $ LCCE.StringEmpty UnicodeRepr))
    let t = LCSC.ACFG args cret q
    return t

translateDecls :: forall arch s . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => PN.NonceGenerator IO s -> LCF.HandleAllocator -> [SA.SomeStubsFunction] -> IO (LCSC.ParsedProgram (DMS.MacawExt arch))
translateDecls ng hAlloc fns = do
    r <- mapM (\(SA.SomeStubsFunction f) -> translateFn @_ @_ @_ @arch ng hAlloc f) fns
    return $ LCSC.ParsedProgram {
        LCSC.parsedProgGlobals = Map.empty,
        LCSC.parsedProgExterns = Map.empty,
        LCSC.parsedProgCFGs = r,
        LCSC.parsedProgForwardDecs = Map.empty
    }

translateProgram :: forall arch s . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => PN.NonceGenerator IO s -> LCF.HandleAllocator -> SA.StubsProgram -> IO (String,LCSC.ParsedProgram (DMS.MacawExt arch))
translateProgram ng halloc prog = do
    p <- translateDecls ng halloc (SA.stubsFnDecls prog)
    return (SA.stubsMain prog, p)


translateFnArgs :: forall arch s args . Ctx.Assignment (LCCR.Atom s) (StubToCrucCtx arch args) -> Ctx.Assignment SA.StubsTypeRepr args -> Ctx.Assignment (StubAtom arch s) args
translateFnArgs catoms tys = case (alist,tlist) of 
    (Ctx.AssignEmpty, Ctx.AssignEmpty) -> Ctx.empty 
    (Ctx.AssignExtend arest a, Ctx.AssignExtend trest t) -> Ctx.extend ( translateFnArgs arest trest) (StubAtom a t)
    where 
        alist = Ctx.viewAssign catoms 
        tlist = Ctx.viewAssign tys