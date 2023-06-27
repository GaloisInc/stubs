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
{-# LANGUAGE BlockArguments #-}

module Stubs.Translate (
 translateExpr,
 translateDecls,
 translateFn,
 translateStmt,
 translateStmts,
 translateProgram,
 CrucibleProgram(..),
 SomeWrappedOverride(..),
 WrappedOverride(..)
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
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.Simulator as LCS
import qualified What4.Interface as WI
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Stubs.Preamble as SPR
import qualified What4.Expr.Builder
import qualified Stubs.Translate.Core as SA
import qualified Stubs.Translate.Core as STC

data CrucibleProgram arch = CrucibleProgram {
  crCFGs :: [LCSC.ACFG (DMS.MacawExt arch)],
  crGlobals :: Map.Map LCSA.GlobalName (Some LCCC.GlobalVar),
  crExterns :: Map.Map LCSA.GlobalName (Some LCCC.GlobalVar),
  crFwdDecs :: Map.Map WF.FunctionName LCF.SomeHandle,
  -- ^ From LCSC.ParsedProgram 
  crFnHandleMap :: [SomeWrappedOverride arch],
  crEntry :: String -- name of entry point
}

data SomeWrappedOverride arch = forall args ret . SomeWrappedOverride(WrappedOverride arch args ret)
data WrappedOverride arch args ret = WrappedOverride (forall sym bak solver scope st fs p r . (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym) =>
    bak -> LCS.Override p sym (DMS.MacawExt arch) (STC.ArchTypeMatchCtx arch args) (STC.ArchTypeMatch arch ret)) (StubHandle arch args ret)

-- Unexported Internal Function
translateExpr' :: forall arch s ret b sret args . (b ~ ArchTypeMatch arch sret, LCCE.IsSyntaxExtension(DMS.MacawExt arch)) => SA.StubsExpr sret -> StubsM arch s args ret (LCCR.Atom s b)
translateExpr' e = do
    regMap <- gets stRegMap
    argmap <- gets stParams
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
        SA.AppExpr f args retty -> do
            knownFns <- gets stFns
            case Map.lookup f knownFns of
                Just (SomeHandle(StubHandle argtys ret h)) -> do
                    -- type checking call
                    Just P.Refl <- return $ P.testEquality ret retty
                    Just P.Refl <- return $ P.testEquality argtys (SA.stubsAssignmentToTys args)
                    -- translate exprs
                    cex <- translateExprs args
                    let t = LCCR.App $ LCCE.HandleLit h
                    ccall <- LCCG.call t cex
                    LCCG.mkAtom ccall
                Nothing -> error "call to unknown function"
        _ -> do
            ce <- translateExpr'' e
            LCCG.mkAtom ce
    where
        translateExpr'' :: forall ext. (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext) => SA.StubsExpr sret -> StubsM arch s args ret (LCCR.Expr (DMS.MacawExt arch) s b)
        translateExpr'' e' = do
            let n = DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)
            return $ case e' of
                SA.BoolLit b -> LCCR.App $ LCCE.BoolLit b
                SA.UnitLit -> LCCR.App LCCE.EmptyApp
                SA.IntLit i -> LCCR.App (LCCE.IntegerToBV n $ LCCR.App $ LCCE.IntLit i)
                SA.VarLit _ -> error "internal translateExpr called on VarLit"
                SA.ArgLit _ -> error "internal translateExpr called on ArgLit"
                SA.AppExpr {} -> error "internal translateExpr called on AppExpr"

translateExpr  :: forall arch s ret b sret ext args . (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext) => SA.StubsExpr sret -> StubsM arch s args ret (LCCR.Expr (DMS.MacawExt arch) s b)
translateExpr e = do
    cache <- gets stAtomCache
    case MapF.lookup e cache of
        Nothing -> do
            t <- translateExpr' e
            updateCache (MapF.insert e (StubAtom t (SA.stubsExprToTy e)))
            return $ LCCG.AtomExpr t
        Just (StubAtom t _) -> return $ LCCG.AtomExpr t

translateExprs :: (cctx ~ ArchTypeMatchCtx arch ctx) => Ctx.Assignment SA.StubsExpr ctx -> StubsM arch s args ret (Ctx.Assignment (LCCR.Expr (DMS.MacawExt arch) s) cctx)
translateExprs eAssign = case elist of
    Ctx.AssignEmpty -> return Ctx.empty
    Ctx.AssignExtend erest e -> do
        e' <- translateExpr e
        er' <- translateExprs erest
        return $ Ctx.extend er' e'
    where elist = Ctx.viewAssign eAssign

updateRegs :: (MapF.MapF SA.StubsVar (StubReg arch s) -> MapF.MapF SA.StubsVar (StubReg arch s)) -> StubsM arch s args ret ()
updateRegs f = modify $ \s -> s {stRegMap = f (stRegMap s)}

updateCache :: (MapF.MapF SA.StubsExpr (StubAtom arch s) -> MapF.MapF SA.StubsExpr (StubAtom arch s)) -> StubsM arch s args ret ()
updateCache f = modify $ \s -> s {stAtomCache = f (stAtomCache s)}

translateStmt :: forall arch s ret args . SA.StubsStmt  -> StubsM arch s args (ArchTypeMatch arch ret) ()
translateStmt stmt = withReturn $ \retty -> do
    regMap <- gets stRegMap
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
                        updateRegs (MapF.insert v (StubReg reg (SA.varType v)))
                Just (StubReg reg _) -> do
                    _ <- LCCG.assignReg reg ce
                    return ()
        SA.ITE c t e -> do
            cond <- translateExpr c
            LCCG.ifte_ cond (translateStmts @_ @_ @ret t) (translateStmts @_ @_ @ret e)
        SA.Loop c body -> do
            LCCG.while (WF.InternalPos, translateExpr c ) (WF.InternalPos, translateStmts @_ @_ @ret body)

translateStmts :: forall arch s ret args . [SA.StubsStmt] -> StubsM arch s args (ArchTypeMatch arch ret) ()
translateStmts [] = return ()
translateStmts (s:stmts) = do
    _ <- translateStmt @_ @_ @ret s
    translateStmts @_ @_ @ret stmts

translateFn :: forall args ret s arch . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => PN.NonceGenerator IO s -> LCF.HandleAllocator -> Map.Map String (SomeHandle arch )-> StubHandle arch args ret -> SA.StubsFunction args ret ->  IO (LCSC.ACFG (DMS.MacawExt arch))
translateFn ng _ handles hdl SA.StubsFunction{SA.stubFnSig=SA.StubsSignature{SA.sigFnArgTys=argtys, SA.sigFnRetTy=retty},SA.stubFnBody=body}= do
    let e = StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch))
    args <- runReaderT (toCrucibleTyCtx argtys) e
    cret <- runReaderT (toCrucibleTy retty) e
    let StubHandle _ _ handle = hdl
    (LCCR.SomeCFG cfg, aux) <- liftIO $ LCCG.defineFunction WF.InternalPos (Some ng) handle $ \crucArgs -> (StubsState e retty MapF.empty MapF.empty (translateFnArgs crucArgs argtys) handles,
                                                                                                     translateStmts @arch @_ @ret body >> LCCG.reportError (LCCR.App $ LCCE.StringEmpty UnicodeRepr))
    return $ LCSC.ACFG args cret cfg

translateDecls :: forall arch s. (DMS.SymArchConstraints arch, SPR.Preamble arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => PN.NonceGenerator IO s -> LCF.HandleAllocator -> [SA.SomeStubsFunction]-> IO (CrucibleProgram arch)
translateDecls ng hAlloc fns = do
    hdls <- mapM (\(SA.SomeStubsFunction f) -> do
        let sig = SA.stubFnSig f
        h <- mkHandle @arch hAlloc sig
        return (SA.sigFnName sig, SomeHandle @arch (StubHandle @arch (SA.sigFnArgTys sig) (SA.sigFnRetTy sig) h))
        ) fns

    ovMap <- mapM (\(SA.SomeStubsSignature sig) -> do
            hdl <-  mkHandle @arch hAlloc sig
            let q = (SA.sigFnName sig, SomeWrappedOverride $ WrappedOverride (SPR.preambleMap @arch sig ) (StubHandle @arch (SA.sigFnArgTys sig) (SA.sigFnRetTy sig) hdl))
            return q) SPR.stubsPreamble

    let preambleHdls = map (\(n,SomeWrappedOverride(WrappedOverride _ s)) -> (n,SomeHandle s)) ovMap

    let handles = Map.fromList (preambleHdls++hdls)
    r <- mapM (\(SA.SomeStubsFunction f) -> do
        let sig = SA.stubFnSig f
        Just (SomeHandle hdl) <- return $ Map.lookup (SA.sigFnName sig) handles
        StubHandle args ret _ <- return hdl
        case (P.testEquality ret (SA.sigFnRetTy sig), P.testEquality args $ SA.sigFnArgTys sig) of
            (Just P.Refl, Just P.Refl) -> translateFn @_ @_ @s @arch ng hAlloc handles hdl f
            _ -> error "Should not occur: Translating undefined function"
        ) fns
    return $ CrucibleProgram {
        crGlobals = Map.empty,
        crExterns = Map.empty,
        crCFGs = r,
        crFwdDecs = Map.empty,
        crEntry = "",
        crFnHandleMap = map snd ovMap
    }

translateProgram :: forall arch s . (DMS.SymArchConstraints arch,SPR.Preamble arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => PN.NonceGenerator IO s -> LCF.HandleAllocator -> SA.StubsProgram -> IO (CrucibleProgram arch)
translateProgram ng halloc prog = do
    let fns = SA.stubsFnDecls prog
    p <- translateDecls ng halloc fns
    return p{crEntry=SA.stubsMain prog}

mkHandle :: forall arch args ret . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => LCF.HandleAllocator -> SA.StubsSignature args ret -> IO ( LCF.FnHandle (ArchTypeMatchCtx arch args) (ArchTypeMatch arch ret))
mkHandle hAlloc fn = do
    let e = StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch))
    args <- runReaderT (toCrucibleTyCtx (SA.sigFnArgTys fn)) e
    cret <- runReaderT (toCrucibleTy (SA.sigFnRetTy fn)) e
    LCF.mkHandle' hAlloc (WF.functionNameFromText (T.pack (SA.sigFnName fn))) args cret

translateFnArgs :: forall arch s args . Ctx.Assignment (LCCR.Atom s) (ArchTypeMatchCtx arch args) -> Ctx.Assignment SA.StubsTypeRepr args -> Ctx.Assignment (StubAtom arch s) args
translateFnArgs catoms tys = case (alist,tlist) of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) -> Ctx.empty
    (Ctx.AssignExtend arest a, Ctx.AssignExtend trest t) -> Ctx.extend ( translateFnArgs arest trest) (StubAtom a t)
    where
        alist = Ctx.viewAssign catoms
        tlist = Ctx.viewAssign tys