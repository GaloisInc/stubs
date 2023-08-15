{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-|
Description: Lowering from Parser produced AST to Stubs AST 


This module defines a 'lowering' step, which transforms the highlevel AST produced from parsing into a more precise AST, with more type information
-}
module Stubs.Lower where 

import qualified Stubs.AST as SA
import qualified Stubs.WeakAST as SW
import qualified Data.Map as Map
import Data.Parameterized (someSymbol, Some (Some), TestEquality (testEquality), type (:~:) (Refl))
import qualified Data.Text as DT
import Control.Monad.State 
import qualified Data.Parameterized.Context as Ctx
import qualified Stubs.Preamble as SPR
import qualified Data.List as List
import qualified Stubs.Opaque as SO
import qualified Stubs.Parser.Exception as SPE
import Control.Monad.Except
import Unsafe.Coerce (unsafeCoerce)

-- | Top level : Given a module, known globals, and known signatures, generate a StubsModule, and all init fns
lowerModule :: SW.SModule -> [SA.SomeStubsGlobalDecl] -> [SA.SomeStubsSignature]-> StubsParserM (SA.StubsModule, [String]) 
lowerModule smod externGlobals declaredSigs = do 
    types <- lowerTyDecls (SW.tys smod)
    globals <- lowerGlobals (SW.globals smod)
    extSigs <- genExtSigs (SW.externs smod)
    fns <- lowerFns (SW.fns smod) (externGlobals ++ globals) (declaredSigs++extSigs) types
    return (SA.mkStubsModule (SW.moduleName smod) fns types globals, map (\(SW.SFn n _ _ _ _) -> n) $ filter (\(SW.SFn _ _ _ _ f) -> SW.fnInit f) (SW.fns smod) ) 

-- | Lower type declarations 
lowerTyDecls :: [SW.STyDecl] -> StubsParserM [SA.SomeStubsTyDecl]
lowerTyDecls tys = do 
    (decls, _) <- foldM (\(decls, m) (SW.STyDecl v t) -> case t of
        SW.SCustom s -> do 
            Just t <- return $ Map.lookup s m
            Some sy <- return $ someSymbol $ DT.pack v
            Some ty <- lowerType t
            return (SA.SomeStubsTyDecl (SA.StubsTyDecl sy ty):decls,Map.insert v t m)
        _ -> do 
            Some sy <- return $ someSymbol $ DT.pack v
            Some ty <- lowerType t
            return (SA.SomeStubsTyDecl (SA.StubsTyDecl sy ty):decls,Map.insert v t m)
        ) (mempty,mempty) tys
    return decls

-- | Lower global variable definitions
lowerGlobals :: [SW.SGlobalDecl] -> StubsParserM [SA.SomeStubsGlobalDecl] 
lowerGlobals = mapM (\(SW.SGlobalDecl (SW.Var s t)) -> do 
            Some ty <- lowerType t 
            return $ SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl s ty)
         ) 


genSigs :: [SW.SFn] -> StubsParserM [SA.SomeStubsSignature]
genSigs = mapM genSig

genExtSigs :: [SW.SExternDecl] -> StubsParserM [SA.SomeStubsSignature]
genExtSigs = mapM genExtSig

-- | Given a parsed function, produce the equivalent signature
genSig :: SW.SFn -> StubsParserM SA.SomeStubsSignature 
genSig (SW.SFn n args ret _ _) = do 
    Some params <- foldM (\(Some ctx) (SW.Var _ t) -> do 
                        Some ty <- lowerType t
                        return $ Some $ Ctx.extend ctx ty
                    ) (Some Ctx.Empty) args
    Some rety <- lowerType ret 
    return (SA.SomeStubsSignature (SA.StubsSignature n params rety )) 

-- | Given an extern declaration, produce the equivalent signature
genExtSig :: SW.SExternDecl -> StubsParserM SA.SomeStubsSignature 
genExtSig (SW.SExternDecl n ret args) = do 
    Some params <- foldM (\(Some ctx) (SW.Var _ t) -> do 
                        Some ty <- lowerType t
                        return $ Some $ Ctx.extend ctx ty
                    ) (Some Ctx.Empty) args
    Some rety <- lowerType ret 
    return (SA.SomeStubsSignature (SA.StubsSignature n params rety )) 

lowerFns :: [SW.SFn] -> [SA.SomeStubsGlobalDecl] -> [SA.SomeStubsSignature]-> [SA.SomeStubsTyDecl] -> StubsParserM [SA.SomeStubsFunction]
lowerFns fns globs declaredSigs tys = do 
    mapM (\fn -> lowerFn fn (SPR.stubsPreamble ++ declaredSigs) globs tys) fns 

lowerFn :: SW.SFn -> [SA.SomeStubsSignature] -> [SA.SomeStubsGlobalDecl] -> [SA.SomeStubsTyDecl] -> StubsParserM SA.SomeStubsFunction
lowerFn (SW.SFn n params ret body f) sigs globs tys = do
    let args = map (\(idx, var ) -> ParamVar var idx) $ zip [0..] params 
    let globals = map (\(SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl n t)) -> GlobalVar $ SW.Var  n $ stubsTyToWeakTy (Some t)  ) globs
    let initialScope = args:[globals] 
    let state = LowerState {types=tys,knownSigs=sigs,currentFn=n, nonce=0, varScope = initialScope}
    (sbody,_) <- runStateT (lowerStmts body) state
    (SA.SomeStubsSignature sig) <- genSig (SW.SFn n params ret body f)
    return $ SA.SomeStubsFunction (SA.StubsFunction{
        SA.stubFnSig= sig,
        SA.stubFnBody=sbody,
        SA.stubFnPrivate=SW.fnPrivate f
    })

lowerStmts :: [SW.Stmt] -> StubsLowerSM [SA.StubsStmt]
lowerStmts = mapM lowerStmt

bumpNonce :: StubsLowerSM String
bumpNonce = do 
    lst <- get
    i <- gets nonce 
    put lst{nonce=i+1}
    return $  "_"++ show i

-- | Lower a single statement. This alongside lowerExpr is the core of the translation
-- Assignments in the 'weak' AST are less precise than in Stubs' AST, as globals, locals, and arguments need to be handled differently.  
-- Thus, we need to identify the kind of variable in question, to determine what to produce.
-- Additionally, StubsExprs are typed, whereas the weak Expr is untyped, so some type checking is necessary.
lowerStmt :: SW.Stmt -> StubsLowerSM SA.StubsStmt
lowerStmt stmt = do 
    lst <- get
    case stmt of 
        SW.Return e -> do 
            Some le <- lowerExpr e 
            return (SA.Return le)
        SW.ITE c t e -> do 
            Some cle <- lowerExpr c 
            let isBool =  testEquality SA.StubsBoolRepr (SA.stubsExprToTy cle)
            case isBool of 
                Just Refl -> do 
                    put lst{varScope=extendScope(varScope lst)}
                    cthen <- lowerStmts t
                    put lst{varScope=extendScope(varScope lst)}
                    celse <- lowerStmts e 
                    put lst{varScope=varScope lst} -- restore
                    return (SA.ITE cle cthen celse)
                Nothing -> do 
                    actual <- exprToTy c
                    throwError $ SPE.TypeMismatch c SW.SBool actual
        SW.Loop c body -> do 
            Some cle <- lowerExpr c
            let isBool = testEquality SA.StubsBoolRepr (SA.stubsExprToTy cle)
            case isBool of 
                Just Refl -> do 
                    put lst{varScope=extendScope(varScope lst)}
                    cb <- lowerStmts body 
                    put lst{varScope=varScope lst} -- restore
                    return (SA.Loop cle cb)
                Nothing -> do 
                    actual <- exprToTy c
                    throwError $ SPE.TypeMismatch c SW.SBool actual
        SW.Assignment s e | "_" <- s -> do 
            Some cle <- lowerExpr e
            wc <- bumpNonce
            return (SA.Assignment (SA.StubsVar wc (SA.stubsExprToTy cle) ) cle )
        SW.Assignment s e -> do 
            Some cle <- lowerExpr e
            -- lookup s: argument? global? local?
            case lookupVar s (varScope lst) of 
                Nothing -> throwError $ SPE.MissingVariable (currentFn lst) s
                Just (ParamVar _ _) -> throwError (SPE.ArgumentAssignment (currentFn lst) s)
                Just (GlobalVar (SW.Var _ t)) -> do 
                    Some ty <- lift $ lowerType t
                    return (SA.GlobalAssignment (SA.StubsVar s ty) cle)
                Just (LocalVar (SW.Var _ t)) -> do 
                    Some ty <- lift $ lowerType t
                    return (SA.Assignment (SA.StubsVar s ty) cle)
        SW.Declaration s t e -> do 
            let nsc = insertScope (LocalVar (SW.Var s t)) (varScope lst)
            Some cle <- lowerExpr e
            put lst{varScope=nsc}
            Some ty <- lift $ lowerType t
            return (SA.Assignment (SA.StubsVar s ty) cle)
            

lowerExprs :: [SW.Expr] -> StubsLowerSM (Some (Ctx.Assignment SA.StubsExpr))
lowerExprs exprs = do 
    foldM (\(Some ctx) e -> do 
            Some ce <- lowerExpr e  
            return$ Some $ Ctx.extend ctx ce) (Some Ctx.empty) exprs 

exprToTy :: SW.Expr -> StubsLowerSM SW.SType 
exprToTy e = do
    lst <- get
    case e of 
        SW.IntLit _ -> pure SW.SInt 
        SW.LongLit _ -> pure SW.SLong 
        SW.ShortLit _ ->  pure SW.SShort
        SW.UIntLit _ -> pure SW.SUInt 
        SW.ULongLit _ -> pure SW.SULong
        SW.UShortLit _ -> pure SW.SUShort
        SW.BoolLit _ -> pure SW.SBool
        SW.UnitLit -> pure SW.SUnit
        SW.Call f args -> do 
            Some sargs <- lowerExprs args
            let t = SA.stubsAssignmentToTys sargs
            sigs <- gets knownSigs
            case lookupFn sigs f t of 
                Nothing -> do -- could be due to aliases 
                    -- need to reify assignment
                    knownTys <- gets types
                    Some rt <- liftIO $ SO.reifyAssignmentTys (Some t) knownTys
                    case lookupFn sigs f rt of
                        Just (SA.SomeStubsSignature (SA.StubsSignature _ _ r)) -> return (stubsTyToWeakTy (Some r))
                        Nothing -> do 
                            fnName <- gets currentFn 
                            throwError $ SPE.MissingFunction fnName f t
                Just (SA.SomeStubsSignature (SA.StubsSignature _ _ r)) -> return (stubsTyToWeakTy (Some r))
        SW.StVar v -> do 
            -- need to find out what v is in order to pull a type
            case lookupVar v (varScope lst) of 
                Nothing -> throwError $ SPE.MissingVariable (currentFn lst) v
                Just (ParamVar (SW.Var _ t) _) -> pure t
                Just (LocalVar (SW.Var _ t)) -> pure t 
                Just (GlobalVar (SW.Var _ t)) -> pure t
        SW.TupleExpr t -> do 
            tys <-  mapM exprToTy t
            return $ SW.STuple tys
        SW.TupleAccessExpr t idx -> do 
            tupty <- exprToTy t 
            case tupty of  
                SW.STuple internal -> do 
                    if idx >= length internal || idx < 0 then throwError $ SPE.TupleIndexOutOfBounds tupty idx else do 
                        return (internal !! idx)
                SW.SCustom alias -> do  -- Lookup custom types
                    Some stubsTy <- lift $ lowerType tupty
                    SA.SomeStubsTypeRepr rt <- pure $ SO.reifyType stubsTy (types lst)
                    case rt of 
                        SA.StubsTupleRepr c -> do 
                            let sctx = assignmentToList (Some c)
                            if idx >= length sctx || idx <0 then throwError $ SPE.TupleIndexOutOfBounds tupty idx else do
                                let i =  sctx !! idx
                                return $ stubsTyToWeakTy i
                        _ -> throwError $ SPE.ExpectedTuple (SW.SCustom alias) (currentFn lst)
                other -> throwError $ SPE.ExpectedTuple other (currentFn lst)
    where  
        assignmentToList = reverse . assignmentToListR
        assignmentToListR :: Some (Ctx.Assignment SA.StubsTypeRepr) -> [Some SA.StubsTypeRepr] 
        assignmentToListR (Some ctx) = case Ctx.viewAssign ctx of 
            Ctx.AssignEmpty -> []
            Ctx.AssignExtend a b -> Some b: assignmentToListR (Some a)
-- | Lower a single expression 
-- Calls and Variables are the interesting cases, as we need to lookup return types, and determine if the variable is a global, a local, or a parameter.
lowerExpr :: SW.Expr -> StubsLowerSM (Some SA.StubsExpr)
lowerExpr e = do 
    lst <- get
    case e of 
        SW.IntLit i -> return $ Some (SA.LitExpr (SA.IntLit i))
        SW.BoolLit b -> return $ Some (SA.LitExpr (SA.BoolLit b))
        SW.LongLit l -> return $ Some (SA.LitExpr (SA.LongLit l))
        SW.ShortLit s -> return $ Some (SA.LitExpr (SA.ShortLit s))
        SW.ULongLit l -> return $ Some (SA.LitExpr (SA.ULongLit l))
        SW.UShortLit s -> return $ Some (SA.LitExpr (SA.UShortLit s))
        SW.UIntLit i -> return $ Some (SA.LitExpr (SA.UIntLit i))
        SW.UnitLit -> return $ Some (SA.LitExpr SA.UnitLit)
        SW.Call f args -> do 
            Some sargs <- lowerExprs args
            let t = SA.stubsAssignmentToTys sargs
            sigs <- gets knownSigs
            case lookupFn sigs f t of 
                Nothing -> do -- could be due to aliases 
                    -- need to reify assignment
                    knownTys <- gets types
                    Some rt <- liftIO $ SO.reifyAssignmentTys (Some t) knownTys
                    case lookupFn sigs f rt of
                        Just (SA.SomeStubsSignature (SA.StubsSignature _ _ r)) -> return $ Some (SA.AppExpr f sargs r)
                        Nothing -> do 
                            fnName <- gets currentFn 
                            throwError $ SPE.MissingFunction fnName f t
                Just (SA.SomeStubsSignature (SA.StubsSignature _ _ r)) -> return $ Some (SA.AppExpr f sargs r)
        SW.StVar v -> do 
            -- Is v an argument, global, or local? if none, error out
            case lookupVar v (varScope lst) of 
                Nothing -> throwError $ SPE.MissingVariable (currentFn lst) v
                Just (ParamVar (SW.Var _ t) i) -> do 
                    Some st <- lift $ lowerType t
                    return $ Some (SA.ArgLit (SA.StubsArg i st))
                Just (LocalVar (SW.Var _ t)) -> do 
                    Some st <- lift $ lowerType t
                    return $ Some (SA.VarLit (SA.StubsVar v st))
                Just (GlobalVar (SW.Var _ t)) -> do 
                    Some st <- lift $ lowerType t
                    return $ Some (SA.GlobalVarLit (SA.StubsVar v st))
        SW.TupleExpr texprs -> do 
            Some stexprs <- lowerExprs texprs 
            return (Some $ SA.TupleExpr stexprs)
        SW.TupleAccessExpr tup idx -> do 
            tupty <- exprToTy tup 
            case tupty of 
                SW.STuple internalTys -> do 
                    if idx >= length internalTys || idx < 0 then throwError $ SPE.TupleIndexOutOfBounds tupty idx else do 
                        Some struct <- lowerExpr tup
                        Some accessSTy <- lift $ lowerType (internalTys !! idx)
                        --TODO: May need type family in order to remove unsafeCoerce here
                        return (Some $ SA.TupleAccessExpr (unsafeCoerce struct) (fromIntegral idx) accessSTy)
                SW.SCustom alias -> do  -- Lookup custom types
                    Some stubsTy <- lift $ lowerType tupty
                    SA.SomeStubsTypeRepr rt <- pure $ SO.reifyType stubsTy (types lst)
                    case rt of 
                        SA.StubsTupleRepr c -> do
                            Some struct <- lowerExpr tup
                            let sctx = assignmentToList (Some c)
                            if idx >= length sctx || idx <0 then throwError $ SPE.TupleIndexOutOfBounds tupty idx else do
                                Some i <- pure $ sctx !! idx
                                return (Some $ SA.TupleAccessExpr (unsafeCoerce struct) idx i)
                        _ -> throwError $ SPE.ExpectedTuple (SW.SCustom alias) (currentFn lst)
                other -> throwError $ SPE.ExpectedTuple other (currentFn lst)
    where  
        assignmentToList = reverse . assignmentToListR
        assignmentToListR :: Some (Ctx.Assignment SA.StubsTypeRepr) -> [Some SA.StubsTypeRepr] 
        assignmentToListR (Some ctx) = case Ctx.viewAssign ctx of 
            Ctx.AssignEmpty -> []
            Ctx.AssignExtend a b -> Some b: assignmentToListR (Some a)
    
lookupFn :: [SA.SomeStubsSignature] -> String -> Ctx.Assignment SA.StubsTypeRepr args -> Maybe SA.SomeStubsSignature 
lookupFn [] _ _ = Nothing 
lookupFn ((SA.SomeStubsSignature (SA.StubsSignature v params r)):sigs) name args = do
    case (testEquality params args, name ==v) of 
        (Just Refl, True) -> Just (SA.SomeStubsSignature (SA.StubsSignature v params r)) 
        _ -> lookupFn sigs name args


-- Translate Types to TypeRepr, as the Stubs AST has typed expressions
lowerType :: SW.SType -> StubsParserM (Some SA.StubsTypeRepr)
lowerType t = case t of 
    SW.SInt -> pure $ Some SA.StubsIntRepr
    SW.SBool -> pure $ Some SA.StubsBoolRepr
    SW.SUInt -> pure $ Some SA.StubsUIntRepr
    SW.SShort-> pure $ Some SA.StubsShortRepr
    SW.SUShort -> pure $ Some SA.StubsUShortRepr
    SW.SLong-> pure $ Some SA.StubsLongRepr
    SW.SULong -> pure $ Some SA.StubsULongRepr
    SW.SUnit -> pure $ Some SA.StubsUnitRepr
    SW.SCustom s -> do 
        Some sy <- return $ someSymbol $ DT.pack s 
        pure $ Some (SA.StubsAliasRepr sy)
    SW.SIntrinsic s -> do 
        Some sy <- return $ someSymbol $ DT.pack s 
        pure $ Some (SA.StubsIntrinsicRepr sy)
    SW.STuple tuptys -> do 
        stys <- mapM lowerType tuptys 
        Some styCtx <- listToAssignment stys 
        return $ Some (SA.StubsTupleRepr styCtx)
    where 
        listToAssignment = listToAssignmentR . reverse
        listToAssignmentR :: [Some SA.StubsTypeRepr] -> StubsParserM (Some (Ctx.Assignment SA.StubsTypeRepr))
        listToAssignmentR [] = pure $ Some Ctx.empty
        listToAssignmentR (Some sty:stys) = do 
            Some rest <- listToAssignmentR stys 
            return (Some $ Ctx.extend rest sty)

-- | Reverse Type matching
stubsTyToWeakTy :: Some SA.StubsTypeRepr -> SW.SType 
stubsTyToWeakTy (Some sty) = case sty of 
    SA.StubsIntRepr -> SW.SInt 
    SA.StubsUIntRepr -> SW.SUInt 
    SA.StubsLongRepr -> SW.SLong
    SA.StubsShortRepr -> SW.SShort
    SA.StubsULongRepr -> SW.SULong
    SA.StubsUShortRepr -> SW.SUShort
    SA.StubsUnitRepr -> SW.SUnit
    SA.StubsBoolRepr -> SW.SBool 
    SA.StubsAliasRepr s -> SW.SCustom $ show s
    SA.StubsIntrinsicRepr s -> SW.SIntrinsic $ show s
    SA.StubsTupleRepr stuptys -> SW.STuple $ assignToList (Some stuptys) 
    where 
        assignToList :: Some (Ctx.Assignment SA.StubsTypeRepr) -> [SW.SType]
        assignToList (Some t) = case Ctx.viewAssign t of 
            Ctx.AssignEmpty -> []
            Ctx.AssignExtend rest h -> stubsTyToWeakTy (Some h) : assignToList (Some rest)

    
-- | State needed for lowering of functions
data LowerState = LowerState {
    types :: [SA.SomeStubsTyDecl],
    varScope :: LowerScope,
    knownSigs :: [SA.SomeStubsSignature],
    nonce :: Int, -- for code gen with wildcards
    currentFn :: String -- useful for exception handling
}

data VarType where 
    LocalVar :: SW.Var -> VarType
    GlobalVar :: SW.Var -> VarType
    ParamVar :: SW.Var -> Int -> VarType

type LowerScope = [[VarType]]

-- TODO: define lookup, cleanup other stuff

matchesVar :: VarType -> String  -> Bool 
matchesVar (LocalVar (SW.Var s _)) v = s == v 
matchesVar (GlobalVar (SW.Var s _)) v = s == v 
matchesVar (ParamVar (SW.Var s _) _) v = s == v

lookupVar :: String -> LowerScope -> Maybe VarType 
lookupVar _ [] = Nothing 
lookupVar s (scope:scopes) = case List.find (\x -> matchesVar x s) scope of 
        Nothing -> lookupVar s scopes 
        Just a -> Just a
    where 
        matchesVar (LocalVar (SW.Var s _)) v = s == v 
        matchesVar (GlobalVar (SW.Var s _)) v = s == v 
        matchesVar (ParamVar (SW.Var s _) _) v = s == v 

extendScope :: LowerScope -> LowerScope
extendScope s = []:s  

insertScope v (x:xs) = (v:x):xs -- partial, assume an initial scope exists (non-empty)

popScope (_:xs) = xs --partial, fails on empty scope

type StubsParserM = (ExceptT SPE.ParserException IO)
type StubsLowerSM = (StateT LowerState StubsParserM)