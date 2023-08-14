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
 SomePreambleOverride(..),
 PreambleOverride(..),
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
import qualified Data.List as List
import qualified Data.Graph as Graph
import qualified Data.Set as Set
import qualified Stubs.Opaque as SO
import qualified Stubs.Translate.Intrinsic as STI
import qualified Stubs.Common as SC
import qualified Lang.Crucible.Types as LCT

-- | A translated Program. Several fields are taken from crucible-syntax's ParsedProgram, for easy conversion
data CrucibleProgram arch = CrucibleProgram {
  -- | The generated CFGs
  crCFGs :: [LCSC.ACFG (DMS.MacawExt arch)],
  crGlobals :: Map.Map LCSA.GlobalName (Some LCCC.GlobalVar),
  crExterns :: Map.Map LCSA.GlobalName (Some LCCC.GlobalVar),
  crFwdDecs :: Map.Map WF.FunctionName LCF.SomeHandle,
  -- | Handle information for preamble, necessary for linking
  crFnHandleMap :: [SomePreambleOverride arch],
  -- | Name of the entry point CFG
  crEntry :: String,
  crOvHandleMap :: [SomeWrappedOverride arch],
  -- | Names of initialization functions
  crInit :: [String],
  crOvInits :: [String]
}

-- | A translated library / module. This is the result of translating a StubsLibrary
data CrucibleLibrary arch = CrucibleLibrary {
    -- | Generated CFGs
    crLibCFGs :: [LCSC.ACFG (DMS.MacawExt arch)],
    -- | Signature and Handle information for defined CFGs, for linking
    crExportedHandles :: [(String,STC.SomeHandle arch)]
}

data SomePreambleOverride arch = forall args ret . SomePreambleOverride(PreambleOverride arch args ret)

data PreambleOverride arch args ret = PreambleOverride (forall sym bak solver scope st fs p . (bak ~ LCBO.OnlineBackend solver scope st fs, LCB.HasSymInterface sym bak, WI.IsExprBuilder sym) =>
    bak -> LCS.Override p sym (DMS.MacawExt arch) (STC.ArchTypeMatchCtx arch args) (STC.ArchTypeMatch arch ret)) (StubHandle arch args ret)

data SomeWrappedOverride arch = forall args ret. SomeWrappedOverride(WrappedOverride arch args ret) 
data WrappedOverride arch args ret = WrappedOverride (forall sym p . SC.Sym sym -> LCS.Override p sym (DMS.MacawExt arch) (STC.ArchTypeMatchCtx arch args) (ArchTypeMatch arch ret)) (StubHandle arch args ret)

-- Unexported Internal Function. A mix of returing Atoms vs Expr causes this hierarchy to be necessary
translateExpr' :: forall arch s ret b sret args. (b ~ ArchTypeMatch arch sret, LCCE.IsSyntaxExtension(DMS.MacawExt arch), STC.StubsArch arch) => SA.StubsExpr sret -> StubsM arch s args ret (LCCR.Atom s b)
translateExpr' e = do
    regMap <- gets stRegMap
    argmap <- gets stParams
    env <- gets stStubsenv
    refMap <- gets stRefMap
    case e of
        SA.VarLit (SA.StubsVar n vt) -> do
            vcty <- runReaderT (toCrucibleTy vt) env
            case MapF.lookup (SA.CrucibleVar n vcty) regMap of
                Just (CrucReg reg _) -> do
                    t <- LCCG.readReg reg
                    LCCG.mkAtom t
                Nothing -> fail "Undefined VarLit encountered" -- Occurs if an expression uses a variable not previously defined. Could be made unreachable by a parser. 
        SA.GlobalVarLit (SA.StubsVar n vt) -> do
            vcty <- runReaderT (toCrucibleTy vt) env
            case MapF.lookup (SA.CrucibleVar n vcty) refMap of
                Just (CrucibleGlobal globVar _) -> do
                    t <- LCCG.readGlobal globVar
                    LCCG.mkAtom t
                Nothing -> fail "Undefined GlobalVarLit encountered"
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
        SA.TupleExpr (tupl::Ctx.Assignment SA.StubsExpr ctx) -> do 
            struct <- translateTuple tupl
            LCCG.mkAtom struct
        _ -> do
            ce <- translateExpr'' e
            LCCG.mkAtom ce
    where
        translateExpr'' :: forall ext. (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext) => SA.StubsExpr sret -> StubsM arch s args ret (LCCR.Expr (DMS.MacawExt arch) s b)
        translateExpr'' e' = do
            case e' of
                SA.LitExpr l -> return $ STC.translateLit l
                -- These should never happen, exist to satisfy match warning
                SA.VarLit _ -> fail "internal translateExpr called on VarLit"
                SA.ArgLit _ -> fail "internal translateExpr called on ArgLit"
                SA.AppExpr {} -> fail "internal translateExpr called on AppExpr"
                SA.GlobalVarLit _ -> fail "internal translateExpr called on GlobalVarLit"
                SA.TupleExpr _ -> fail "internal translateExpr called on TupleExpr"
        translateTuple :: forall arch ctx a. (STC.ArchTypeMatchCtx arch ctx ~ a, STC.StubsArch arch) => Ctx.Assignment SA.StubsExpr ctx -> StubsM arch s args ret (LCCR.Expr (DMS.MacawExt arch) s (LCT.StructType a))
        translateTuple tupl = do 
            env <- gets stStubsenv
            internals <- translateExprs tupl 
            ctys <- runReaderT (toCrucibleTyCtx $ SA.stubsAssignmentToTys tupl) env
            return $ LCCR.App $ LCCE.MkStruct ctys internals

-- | Translate a single StubsExpr
translateExpr  :: forall arch s ret b sret ext args . (b ~ ArchTypeMatch arch sret, ext ~ DMS.MacawExt arch, LCCE.IsSyntaxExtension ext, STC.StubsArch arch) => SA.StubsExpr sret -> StubsM arch s args ret (LCCR.Expr (DMS.MacawExt arch) s b)
translateExpr e = do
    cache <- gets stAtomCache
    case MapF.lookup e cache of -- only translate exprs once, when possible
        Nothing -> do
            t <- translateExpr' e
            --updateCache (MapF.insert e (StubAtom t (SA.stubsExprToTy e)))
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

updateRegs :: (MapF.MapF SA.CrucibleVar (CrucReg arch s) -> MapF.MapF SA.CrucibleVar (CrucReg arch s)) -> StubsM arch s args ret ()
updateRegs f = modify $ \s -> s {stRegMap = f (stRegMap s)}

updateCache :: (MapF.MapF SA.StubsExpr (StubAtom arch s) -> MapF.MapF SA.StubsExpr (StubAtom arch s)) -> StubsM arch s args ret ()
updateCache f = modify $ \s -> s {stAtomCache = f (stAtomCache s)}

-- | Translate a single StubsStmt
translateStmt :: forall arch s ret args . (STC.StubsArch arch) => SA.StubsStmt  -> StubsM arch s args (ArchTypeMatch arch ret) ()
translateStmt stmt = withReturn $ \retty -> do
    regMap <- gets stRegMap
    env <- gets stStubsenv
    refMap <- gets stRefMap
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
            SA.StubsVar n vt <- return v
            -- Crucible type check
            ecty <- runReaderT (toCrucibleTy (SA.stubsExprToTy e)) env
            vcty <- runReaderT (toCrucibleTy vt) env
            case PN.testEquality vcty ecty of
                Just PN.Refl -> do
                            ce <- translateExpr e
                            let cvar= SA.CrucibleVar n vcty
                            case MapF.lookup cvar regMap of -- Is v in scope already?
                                Nothing -> do
                                    reg <- LCCG.newReg ce
                                    updateRegs (MapF.insert cvar (CrucReg reg (SA.cvarType cvar)))
                                Just (CrucReg reg _) -> do
                                    _ <- LCCG.assignReg reg ce
                                    return ()
                _ -> fail $ "Type mismatch - Expected: " ++ show vt ++ " Actual: " ++ show (SA.stubsExprToTy e)
        SA.GlobalAssignment v e -> do
            SA.StubsVar n vt <- return v
            ecty <- runReaderT (toCrucibleTy (SA.stubsExprToTy e)) env
            vcty <- runReaderT (toCrucibleTy vt) env
            case PN.testEquality vcty ecty of
                Just PN.Refl -> do
                            ce <- translateExpr e
                            case MapF.lookup (SA.CrucibleVar n vcty) refMap of -- Is v defined?
                                Nothing -> fail ("Assignment to nonexistent global: " ++ n)
                                Just (CrucibleGlobal globVar _) -> do
                                    _ <- LCCG.writeGlobal globVar ce
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
                STC.StubsEnv arch ->
                MapF.MapF SA.CrucibleVar (STC.CrucibleGlobal arch) ->
                SA.StubsFunction args ret ->  IO (LCSC.ACFG (DMS.MacawExt arch))
translateFn ng _ handles hdl env gmap SA.StubsFunction{SA.stubFnSig=SA.StubsSignature{SA.sigFnArgTys=argtys, SA.sigFnRetTy=retty},SA.stubFnBody=body}= do
    -- CFG needs crucible type info
    args <- runReaderT (toCrucibleTyCtx argtys) env
    cret <- runReaderT (toCrucibleTy retty) env
    let StubHandle _ _ handle = hdl
    (LCCR.SomeCFG cfg, _) <- liftIO $ LCCG.defineFunction WF.InternalPos (Some ng) handle $ \crucArgs -> (StubsState env retty MapF.empty MapF.empty (translateFnArgs crucArgs argtys) handles gmap,
                                                                                                     translateStmts @arch @_ @ret body >> LCCG.reportError (LCCR.App $ LCCE.StringEmpty UnicodeRepr))
    return $ LCSC.ACFG args cret cfg

-- | Translate all declarations from a StubsLibrary
translateDecls :: forall arch s . (STC.StubsArch arch, SPR.Preamble arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) =>
        PN.NonceGenerator IO s ->
        LCF.HandleAllocator ->
        [(String, SomePreambleOverride arch)] -> -- Override mappings : needed so all modules use the same preamble handles
        [(String, SomeHandle arch)] -> -- Handles for previously translated functions (from modules already processed)
        STC.StubsEnv arch -> 
        MapF.MapF SA.CrucibleVar (STC.CrucibleGlobal arch) ->
        [(String, SomeWrappedOverride arch)] ->
        [SA.SomeStubsFunction] -> -- Functions to translate 
        IO [(LCSC.ACFG (DMS.MacawExt arch), (String,SomeHandle arch))]
translateDecls ng hAlloc preMap prevHdls env gmap ovMap fns = do

    -- get handles for all functions before hand, for linking.
    -- Handles contain an id nonce, so cannot translate signatures in situ
    hdls <- mapM (\(SA.SomeStubsFunction f) -> do
        let sig = SA.stubFnSig f
        h <- mkHandle @arch hAlloc sig env
        return (SA.sigFnName sig, SomeHandle @arch (StubHandle @arch (SA.sigFnArgTys sig) (SA.sigFnRetTy sig) h))
        ) fns

    -- Build handle map for preamble linking.
    let preambleHdls = map (\(n,SomePreambleOverride(PreambleOverride _ s)) -> (n,SomeHandle s)) preMap

    -- TODO: override handles
    let ovHdls = map (\(n, SomeWrappedOverride(WrappedOverride _ s)) -> (n,SomeHandle s)) ovMap

    let handles = Map.fromList (preambleHdls++ovHdls++prevHdls++hdls)

    -- Generate CFG for each function
    mapM (\(SA.SomeStubsFunction f) -> do
        let sig = SA.stubFnSig f
        Just (SomeHandle hdl) <- return $ Map.lookup (SA.sigFnName sig) handles
        StubHandle args ret _ <- return hdl
        case (P.testEquality ret (SA.sigFnRetTy sig), P.testEquality args $ SA.sigFnArgTys sig) of
            (Just P.Refl, Just P.Refl) -> do
                t <- translateFn @_ @_ @s @arch ng hAlloc handles hdl env gmap f
                return (t,(SA.sigFnName sig,SomeHandle hdl))
            _ -> fail "Should not occur: Translating undefined function"
        ) fns

-- | Translate a single StubsLibrary
translateLibrary :: forall arch s . (STC.StubsArch arch,SPR.Preamble arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) =>
            PN.NonceGenerator IO s ->
            LCF.HandleAllocator ->
            [(String, SomePreambleOverride arch)] ->
            [(String, SomeHandle arch)] ->
            STC.StubsEnv arch ->
            MapF.MapF SA.CrucibleVar (STC.CrucibleGlobal arch) ->
                [(String, SomeWrappedOverride arch)] ->
            SA.StubsModule -> IO (CrucibleLibrary arch)
translateLibrary ng halloc preMap prevHdls env gmap ovMap lib = do
    cfghdls <- translateDecls ng halloc preMap prevHdls env gmap ovMap (SA.fnDecls lib)
    return CrucibleLibrary {
        crLibCFGs=map fst cfghdls,
        crExportedHandles=map snd cfghdls
    }

-- | Translation of an entire StubsProgram. This is the core entry point for translation, and includes 
-- module graph resolution, for externs in each library
translateProgram :: forall arch s . (STC.StubsArch arch,SPR.Preamble arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => PN.NonceGenerator IO s -> LCF.HandleAllocator -> [STI.OverrideModule arch]-> SA.StubsProgram -> IO [CrucibleProgram arch]
translateProgram ng halloc ovs prog = do

    -- 1. Translate Haskell Overrides
    -- 1.1 Collect Intrinsic Definitions, to put into environment
    let intrinsicMap = foldr (\(STI.SomeIntrinsicTyDecl (STI.IntrinsicTyDecl s ct)) acc -> MapF.insert s (STC.coerceToIntrinsic s ct) acc) MapF.empty (concatMap (\(STI.OverrideModule _ _ decls _)-> decls)  ovs)
    -- 1.2 Wrap up override definitions like preamble (Will put this information into CrucibleProgram, as it needs to be linked specially)
    ovMapTpl <- concat <$> mapM (\(STI.OverrideModule _ decls _ _) -> mapM (\(STI.SomeStubsOverride (STI.StubsOverride ovf cargs cret) sig) -> do 
                SA.StubsSignature n argtys ret <- return sig
                hdl <-  mkHandle @arch halloc sig (STC.StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)) MapF.empty intrinsicMap)
                --Type Check
                --declared
                argsd <- runReaderT (toCrucibleTyCtx argtys) (STC.StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)) MapF.empty intrinsicMap)
                retd <- runReaderT (toCrucibleTy ret) (STC.StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)) MapF.empty intrinsicMap)

                Just P.Refl <- return $ P.testEquality cargs argsd
                Just P.Refl <- return $ P.testEquality cret retd

                let wrappedOv = WrappedOverride ovf (StubHandle @arch argtys ret hdl)
                return ((n,SomeWrappedOverride wrappedOv),SA.SomeStubsSignature sig)) decls) ovs

    let ovMap = map fst ovMapTpl
    let ovSigs = map snd ovMapTpl
    let ovInits = concatMap STI.ovInits ovs
    --Every lib shares the same preamble handles
    preMap <- mapM (\(SA.SomeStubsSignature sig) -> do
            hdl <-  mkHandle @arch halloc sig (STC.StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)) MapF.empty intrinsicMap)
            let q = (SA.sigFnName sig, SomePreambleOverride $ PreambleOverride (SPR.preambleMap @arch sig ) (StubHandle @arch (SA.sigFnArgTys sig) (SA.sigFnRetTy sig) hdl))
            return q) SPR.stubsPreamble

    let libs = SA.stubsModules prog
    -- Enforce Opaque Types
    foldM_ (\_ lib -> unless (SO.satOpaque lib) $ fail ("Opaqueness check failed for library: " ++ show (SA.moduleName lib))) () libs

    -- Verify Signatures (enforces opacity for calls as well)
    let expectedSigs = Set.difference (Set.fromList $ concatMap SA.externSigs libs) (Set.union (Set.fromList SPR.stubsPreamble) (Set.fromList ovSigs))
    let definedSigs = Set.fromList $ concatMap SA.stubsLibDefs libs
    let undefinedSigs = Set.toList $ Set.difference expectedSigs definedSigs

    --TODO: handle opaque issues separate 
    let tys = concatMap SA.tyDecls libs
    t <- mapM (\sig -> SO.reifySig sig tys) undefinedSigs
    let missingSigs = Set.toList $ Set.difference (Set.fromList t) (Set.union (Set.union (Set.fromList SPR.stubsPreamble) (Set.fromList ovSigs)) definedSigs)
    Control.Monad.RWS.when (not (null missingSigs)) $ fail ("Missing signatures: " ++ show missingSigs) --Note: This shows the types after removing opaques, so may be unhelpful. The parser is intended to catch this sort of thing

    -- Collect aliases/opaques
    let tyMap = foldr (\(SA.SomeStubsTyDecl (SA.StubsTyDecl s t)) acc -> MapF.insert s (STC.coerceToAlias s t) acc) MapF.empty tys

    let env = STC.StubsEnv @arch (DMC.memWidthNatRepr @(DMC.ArchAddrWidth arch)) tyMap intrinsicMap
    -- Topological sort of module/lib graph
    let dependencyList = map (\ lib -> (lib,filter (\olib -> not $ List.null $ List.intersect (SA.stubsLibDefs olib) (SA.externSigs lib))
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
    let orderedLibs = map (\v' -> case vl v' of
            (l,_,_)-> l
            ) $ Graph.topSort $ Graph.transposeG g'
    --Global variable initialization
    globalMap <- translateGlobals @arch halloc env (concatMap SA.globalDecls libs)


    -- Translate libraries
    translatedLibs <- foldM (\ (tlibs,acc) lib -> do
                translated <- translateLibrary ng halloc preMap acc env globalMap ovMap lib
                let cfgs = crLibCFGs translated
                let accHdls = crExportedHandles translated
                return (cfgs++tlibs,accHdls++acc)
            ) ([],[]) orderedLibs

    let crucProgs = map (\s -> CrucibleProgram{crEntry=s,crFnHandleMap=map snd preMap, crCFGs=fst translatedLibs,crExterns=mempty, crGlobals=mempty,crFwdDecs=mempty, crOvHandleMap = map snd ovMap, crInit=(SA.stubsInitFns prog), crOvInits=ovInits}) (SA.stubsEntryPoints prog)
    return crucProgs

mkHandle :: forall arch args ret . (STC.StubsArch arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => LCF.HandleAllocator -> SA.StubsSignature args ret -> STC.StubsEnv arch-> IO ( LCF.FnHandle (ArchTypeMatchCtx arch args) (ArchTypeMatch arch ret))
mkHandle hAlloc fn env = do
    args <- runReaderT (toCrucibleTyCtx (SA.sigFnArgTys fn)) env
    cret <- runReaderT (toCrucibleTy (SA.sigFnRetTy fn)) env
    LCF.mkHandle' hAlloc (WF.functionNameFromText (T.pack (SA.sigFnName fn))) args cret

translateFnArgs :: forall arch s args . Ctx.Assignment (LCCR.Atom s) (ArchTypeMatchCtx arch args) -> Ctx.Assignment SA.StubsTypeRepr args -> Ctx.Assignment (StubAtom arch s) args
translateFnArgs catoms tys = case (alist,tlist) of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) -> Ctx.empty
    (Ctx.AssignExtend arest a, Ctx.AssignExtend trest t) -> Ctx.extend ( translateFnArgs arest trest) (StubAtom a t)
    where
        alist = Ctx.viewAssign catoms
        tlist = Ctx.viewAssign tys

-- Generate global variable ref cells 
translateGlobals ::forall arch . (STC.StubsArch arch, LCCE.IsSyntaxExtension (DMS.MacawExt arch)) => LCF.HandleAllocator -> STC.StubsEnv arch -> [SA.SomeStubsGlobalDecl] -> IO (MapF.MapF SA.CrucibleVar (STC.CrucibleGlobal arch))
translateGlobals halloc env globals = do
    foldM (\acc (SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl g ty)) -> do
            cty <- runReaderT (toCrucibleTy @arch ty) env
            let v = SA.CrucibleVar g cty
            gvar <- LCCC.freshGlobalVar halloc (T.pack g) cty
            return $ MapF.insert v (STC.CrucibleGlobal gvar cty) acc
            ) MapF.empty globals
