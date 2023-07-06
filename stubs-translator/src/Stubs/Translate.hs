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
{-# LANGUAGE LambdaCase #-}

{-|
Description: Core Translation from Stubs to Crucible

This module contains the translation from the Stubs language into Crucible. Given a StubsProgram,  
an equivalent CrucibleProgram is produced, which contains Crucible CFGs alongside information needed for linking,
as well as for symbolic execution
-}
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
import qualified Stubs.Translate.Core as STC
import Stubs.AST (stubsLibDefs)
import qualified Data.List as List
import qualified Data.Graph as Graph
import qualified Data.Set as Set

-- | A translated Program. Several fields are taken from crucible-syntax's ParsedProgram, for easy conversion
data CrucibleProgram arch = CrucibleProgram {
  -- | The generated CFGs
  crCFGs :: [LCSC.ACFG (DMS.MacawExt arch)],
  crGlobals :: Map.Map LCSA.GlobalName (Some LCCC.GlobalVar),
  crExterns :: Map.Map LCSA.GlobalName (Some LCCC.GlobalVar),
  crFwdDecs :: Map.Map WF.FunctionName LCF.SomeHandle,
  -- | Handle information for preamble, necessary for linking
  crFnHandleMap :: [SomeWrappedOverride arch],
  -- | Name of the entry point CFG
  crEntry :: String
}

-- | A translated library / module. This is the result of translating a StubsLibrary
data CrucibleLibrary arch = CrucibleLibrary {
    -- | Generated CFGs
    crLibCFGs :: [LCSC.ACFG (DMS.MacawExt arch)],
    -- | Signature and Handle information for defined CFGs, for linking
    crExportedHandles :: [(String,STC.SomeHandle arch)]
}

data SomeWrappedOverride arch = forall args ret . SomeWrappedOverride(WrappedOverride arch args ret)
data WrappedOverride arch args ret = WrappedOverride (forall sym bak solver scope st fs p . (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym) =>
    bak -> LCS.Override p sym (DMS.MacawExt arch) (STC.ArchTypeMatchCtx arch args) (STC.ArchTypeMatch arch ret)) (StubHandle arch args ret)

-- Unexported Internal Function. A mix of returing Atoms vs Expr causes this hierarchy to be necessary
translateExpr' :: forall arch s ret b sret args . (b ~ ArchTypeMatch arch sret, LCCE.IsSyntaxExtension(DMS.MacawExt arch), STC.StubsArch arch) => SA.StubsExpr sret -> StubsM arch s args ret (LCCR.Atom s b)
translateExpr' e = do
    regMap <- gets stRegMap
    argmap <- gets stParams
    env <- gets stStubsenv
    case e of
        SA.VarLit v -> case MapF.lookup v regMap of
            Just (StubReg reg _) -> do 
                t <- LCCG.readReg reg
                LCCG.mkAtom t
            Nothing -> error "Undefined VarLit encountered" -- Occurs if an expression uses a variable not previously defined. Could be made unreachable by a parser. 
        SA.ArgLit (SA.StubsArg i ty) -> do
            case Ctx.intIndex i (Ctx.size argmap) of
                Nothing -> fail $ "Argument index out of bounds" ++ show i
                Just (Some idx) -> do
                    StubAtom a sty <- return $ argmap Ctx.! idx
                    -- Crucible type equality: needed in presence of opaque types
                    cty <- runReaderT (toCrucibleTy ty) env 
                    csty <- runReaderT (toCrucibleTy sty) env
                    Just P.Refl <- return $ P.testEquality cty csty
                    return a
        SA.AppExpr f args retty -> do
            knownFns <- gets stFns
            case Map.lookup f knownFns of
                Just (SomeHandle(StubHandle argtys ret h)) -> do
                    -- type checking call
                    -- Convert to crucible types in order to type check opaque types
                    knownRet <- runReaderT (STC.toCrucibleTy @arch ret) env
                    decRet <- runReaderT (STC.toCrucibleTy @arch retty) env
                    knownArgs <- runReaderT (toCrucibleTyCtx argtys) env
                    decArgs <- runReaderT (toCrucibleTyCtx $ SA.stubsAssignmentToTys args) env
                    Just P.Refl <- return $ P.testEquality knownRet decRet
                    Just P.Refl <- return $ P.testEquality knownArgs decArgs
                    -- translate exprs
                    cex <- translateExprs args
                    let t = LCCR.App $ LCCE.HandleLit h
                    ccall <- LCCG.call t cex
                    LCCG.mkAtom ccall
                Nothing -> fail $ "call to unknown function: " ++ f -- Top level translation prevents this, but invoking something more internal could cause this
        _ -> do
            ce <- translateExpr'' e
            LCCG.mkAtom ce
    where
        translateExpr'' :: forall ext. (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext) => SA.StubsExpr sret -> StubsM arch s args ret (LCCR.Expr (DMS.MacawExt arch) s b)
        translateExpr'' e' = do
            case e' of
                SA.LitExpr l -> return $ STC.translateLit l
                SA.VarLit _ -> error "internal translateExpr called on VarLit"
                SA.ArgLit _ -> error "internal translateExpr called on ArgLit"
                SA.AppExpr {} -> error "internal translateExpr called on AppExpr"

-- | Translate a single StubsExpr
translateExpr  :: forall arch s ret b sret ext args . (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext, STC.StubsArch arch) => SA.StubsExpr sret -> StubsM arch s args ret (LCCR.Expr (DMS.MacawExt arch) s b)
translateExpr e = do
    cache <- gets stAtomCache
    case MapF.lookup e cache of -- only translate exprs once, when possible
        Nothing -> do
            t <- translateExpr' e
            updateCache (MapF.insert e (StubAtom t (SA.stubsExprToTy e)))
            return $ LCCG.AtomExpr t
        Just (StubAtom t _) -> return $ LCCG.AtomExpr t

-- | Translate an Assignment of StubExpr, mostly for use in function argument translation
translateExprs :: (cctx ~ ArchTypeMatchCtx arch ctx, STC.StubsArch arch) => Ctx.Assignment SA.StubsExpr ctx -> StubsM arch s args ret (Ctx.Assignment (LCCR.Expr (DMS.MacawExt arch) s) cctx)
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

-- | Translate a single StubsStmt
translateStmt :: forall arch s ret args . (STC.StubsArch arch) => SA.StubsStmt  -> StubsM arch s args (ArchTypeMatch arch ret) ()
translateStmt stmt = withReturn $ \retty -> do
    regMap <- gets stRegMap
    env <- gets stStubsenv
    case stmt of
        SA.Return e -> do
            -- Crucible type check, due to opaques
            ecty <- runReaderT (toCrucibleTy (SA.stubsExprToTy e)) env
            rcty <- runReaderT (toCrucibleTy retty) env
            case PN.testEquality rcty ecty of
                Just PN.Refl -> do
                    ce <- translateExpr e
                    LCCG.returnFromFunction ce
                Nothing -> do
                    LCCG.reportError $  LCCR.App $ LCCE.StringEmpty UnicodeRepr
        SA.Assignment v e -> do
            SA.StubsVar _ vt <- return v
            -- Crucible type check
            ecty <- runReaderT (toCrucibleTy (SA.stubsExprToTy e)) env
            vcty <- runReaderT (toCrucibleTy vt) env
            case PN.testEquality vcty ecty of 
                Just PN.Refl -> do  
                            ce <- translateExpr e
                            case MapF.lookup v regMap of -- Is v in scope already?
                                Nothing -> do
                                    reg <- LCCG.newReg ce
                                    updateRegs (MapF.insert v (StubReg reg (SA.varType v)))
                                Just (StubReg reg _) -> do
                                    _ <- LCCG.assignReg reg ce
                                    return ()
                _ -> fail $ "Type mismatch - Expected: " ++ show vt ++ " Actual: " ++ show (SA.stubsExprToTy e)
        SA.ITE c t e -> do
            cond <- translateExpr c
            LCCG.ifte_ cond (translateStmts @_ @_ @ret t) (translateStmts @_ @_ @ret e)
        SA.Loop c body -> do
            LCCG.while (WF.InternalPos, translateExpr c ) (WF.InternalPos, translateStmts @_ @_ @ret body)

-- | Translation of a list of statements, mostly for use in function bodies, loops, and conditionals
translateStmts :: forall arch s ret args . (STC.StubsArch arch) => [SA.StubsStmt] -> StubsM arch s args (ArchTypeMatch arch ret) ()
translateStmts [] = return ()
translateStmts (s:stmts) = do
    _ <- translateStmt @_ @_ @ret s
    translateStmts @_ @_ @ret stmts

-- | Function translation
translateFn :: forall args ret s arch . (DMS.SymArchConstraints arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch),STC.StubsArch arch) =>
                PN.NonceGenerator IO s ->
                LCF.HandleAllocator ->
                Map.Map String (SomeHandle arch )->
                StubHandle arch args ret ->
                MapF.MapF P.SymbolRepr STC.WrappedStubsTypeAliasRepr ->
                SA.StubsFunction args ret ->  IO (LCSC.ACFG (DMS.MacawExt arch))
translateFn ng _ handles hdl aliasMap SA.StubsFunction{SA.stubFnSig=SA.StubsSignature{SA.sigFnArgTys=argtys, SA.sigFnRetTy=retty},SA.stubFnBody=body}= do
    let e = StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)) aliasMap
    -- CFG needs crucible type info
    args <- runReaderT (toCrucibleTyCtx argtys) e
    cret <- runReaderT (toCrucibleTy retty) e
    let StubHandle _ _ handle = hdl
    (LCCR.SomeCFG cfg, _) <- liftIO $ LCCG.defineFunction WF.InternalPos (Some ng) handle $ \crucArgs -> (StubsState e retty MapF.empty MapF.empty (translateFnArgs crucArgs argtys) handles,
                                                                                                     translateStmts @arch @_ @ret body >> LCCG.reportError (LCCR.App $ LCCE.StringEmpty UnicodeRepr))
    return $ LCSC.ACFG args cret cfg

-- | Translate all declarations from a StubsLibrary
translateDecls :: forall arch s. (STC.StubsArch arch, SPR.Preamble arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) =>
        PN.NonceGenerator IO s ->
        LCF.HandleAllocator ->
        [(String, SomeWrappedOverride arch)] -> -- Override mappings : needed so all modules use the same preamble handles
        [(String, SomeHandle arch)] -> -- Handles for previously translated functions (from modules already processed)
         MapF.MapF P.SymbolRepr STC.WrappedStubsTypeAliasRepr -> -- Alias Map
        [SA.SomeStubsFunction] -> -- Functions to translate 
        IO [(LCSC.ACFG (DMS.MacawExt arch), (String,SomeHandle arch))]
translateDecls ng hAlloc ovMap prevHdls aliasMap fns = do

    -- get handles for all functions before hand, for linking.
    -- Handles contain an id nonce, so cannot translate signatures in situ
    hdls <- mapM (\(SA.SomeStubsFunction f) -> do
        let sig = SA.stubFnSig f
        h <- mkHandle @arch hAlloc sig aliasMap
        return (SA.sigFnName sig, SomeHandle @arch (StubHandle @arch (SA.sigFnArgTys sig) (SA.sigFnRetTy sig) h))
        ) fns

    -- Build handle map for preamble linking.
    let preambleHdls = map (\(n,SomeWrappedOverride(WrappedOverride _ s)) -> (n,SomeHandle s)) ovMap

    let handles = Map.fromList (preambleHdls++prevHdls++hdls)

    -- Generate CFG for each function
    mapM (\(SA.SomeStubsFunction f) -> do
        let sig = SA.stubFnSig f
        Just (SomeHandle hdl) <- return $ Map.lookup (SA.sigFnName sig) handles
        StubHandle args ret _ <- return hdl
        case (P.testEquality ret (SA.sigFnRetTy sig), P.testEquality args $ SA.sigFnArgTys sig) of
            (Just P.Refl, Just P.Refl) -> do
                t <- translateFn @_ @_ @s @arch ng hAlloc handles hdl aliasMap f
                return (t,(SA.sigFnName sig,SomeHandle hdl))
            _ -> fail "Should not occur: Translating undefined function"
        ) fns

-- | Translate a single StubsLibrary
translateLibrary :: forall arch s . (STC.StubsArch arch,SPR.Preamble arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) =>
            PN.NonceGenerator IO s ->
            LCF.HandleAllocator ->
            [(String, SomeWrappedOverride arch)] ->
            [(String, SomeHandle arch)] ->
            MapF.MapF P.SymbolRepr STC.WrappedStubsTypeAliasRepr ->
            SA.StubsLibrary -> IO (CrucibleLibrary arch)
translateLibrary ng halloc ovMap prevHdls aliasMap lib = do
    cfghdls <- translateDecls ng halloc ovMap prevHdls aliasMap (SA.fnDecls lib)
    return CrucibleLibrary {
        crLibCFGs=map fst cfghdls,
        crExportedHandles=map snd cfghdls
    }

-- | Translation of an entire StubsProgram. This is the core entry point for translation, and includes 
-- module graph resolution, for externs in each library
translateProgram :: forall arch s . (STC.StubsArch arch,SPR.Preamble arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => PN.NonceGenerator IO s -> LCF.HandleAllocator -> SA.StubsProgram -> IO (CrucibleProgram arch)
translateProgram ng halloc prog = do

    --Every lib shares the same preamble handles
    ovMap <- mapM (\(SA.SomeStubsSignature sig) -> do
            hdl <-  mkHandle @arch halloc sig MapF.empty
            let q = (SA.sigFnName sig, SomeWrappedOverride $ WrappedOverride (SPR.preambleMap @arch sig ) (StubHandle @arch (SA.sigFnArgTys sig) (SA.sigFnRetTy sig) hdl))
            return q) SPR.stubsPreamble

    let libs = SA.stubsLibs prog

    -- Verify Signatures (enforces opacity for calls as well)
    let expectedSigs = Set.difference (Set.fromList $ concatMap SA.externSigs libs) (Set.fromList SPR.stubsPreamble)
    let definedSigs = Set.fromList $ concatMap SA.stubsLibDefs libs
    let undefinedSigs = Set.toList $ Set.difference expectedSigs definedSigs
    Control.Monad.RWS.when (not (null undefinedSigs)) $ fail ("Missing signatures: " ++ show undefinedSigs)

    -- Collect aliases/opaques
    let tyMap = foldr (\(SA.SomeStubsTyDecl (SA.StubsTyDecl s t)) acc -> MapF.insert s (STC.coerceToAlias s t) acc) MapF.empty ( concatMap SA.tyDecls libs)

    -- Topological sort of module/lib graph
    let dependencyList = map (\ lib -> (lib,filter (\olib -> not $ List.null $ List.intersect (stubsLibDefs olib) (SA.externSigs lib))
                 libs)) libs
    let libMapping = fst $ foldr (\lib (acc,idx) -> (Map.insert lib idx acc,idx+1)  ) (Map.empty,0) libs
    v <- mapM (\(l, deps) -> do
        Just libI <- return $ Map.lookup l libMapping
        mdepI <- mapM (\ol -> return (Map.lookup ol  libMapping)) deps
        let depI = map (\case
                Just d -> d
                _ -> error "lost mapping" -- Should be impossible, by the map's construction
                ) mdepI
        return (l,libI, depI)
        ) dependencyList

    let (g',vl,_) = Graph.graphFromEdges v
    let orderedLibs = map (\v -> case vl v of
            (l,_,_)-> l
            ) $ Graph.topSort $ Graph.transposeG g'

    translatedLibs <- foldM (\ (tlibs,acc) lib -> do
                translated <- translateLibrary ng halloc ovMap acc tyMap lib
                let cfgs = crLibCFGs translated
                let accHdls = crExportedHandles translated
                return (cfgs++tlibs,accHdls++acc)
            ) ([],[]) orderedLibs

    return CrucibleProgram{crEntry=SA.stubsMain prog,crFnHandleMap=map snd ovMap, crCFGs=fst translatedLibs,crExterns=mempty, crGlobals=mempty,crFwdDecs=mempty}

mkHandle :: forall arch args ret . (STC.StubsArch arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => LCF.HandleAllocator -> SA.StubsSignature args ret -> MapF.MapF P.SymbolRepr STC.WrappedStubsTypeAliasRepr-> IO ( LCF.FnHandle (ArchTypeMatchCtx arch args) (ArchTypeMatch arch ret))
mkHandle hAlloc fn tyMap = do
    let e = StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)) tyMap
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