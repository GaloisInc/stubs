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

-- | Top level : Given a module, known globals, and known signatures, generate a StubsModule, and all init fns
lowerModule :: SW.SModule -> [SA.SomeStubsGlobalDecl] -> [SA.SomeStubsSignature]-> StubsParserM (SA.StubsModule, [String]) 
lowerModule smod externGlobals declaredSigs = do 
    types <- lowerTyDecls (SW.tys smod)
    globals <- lowerGlobals (SW.globals smod)
    extSigs <- genExtSigs (SW.externs smod)
    fns <- lowerFns (SW.fns smod) (externGlobals ++ globals) (declaredSigs++extSigs) types
    return (SA.mkStubsModule (SW.moduleName smod) fns types globals, map (\(SW.SFn n _ _ _ _) -> n) $ filter (\(SW.SFn _ _ _ _ f) -> f) (SW.fns smod) ) 

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
    let state = LowerState {globals=globs, types=tys,knownSigs=sigs, arguments=params, inScopeVars=[],currentFn=n}
    (sbody,_) <- runStateT (lowerStmts body) state
    (SA.SomeStubsSignature sig) <- genSig (SW.SFn n params ret body f)
    return $ SA.SomeStubsFunction (SA.StubsFunction{
        SA.stubFnSig= sig,
        SA.stubFnBody=sbody
    })

lowerStmts :: [SW.Stmt] -> StubsLowerSM [SA.StubsStmt]
lowerStmts = mapM lowerStmt

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
            Just Refl <- return $ testEquality SA.StubsBoolRepr (SA.stubsExprToTy cle)
            ct <- lowerStmts t 
            ce <- lowerStmts e 
            return (SA.ITE cle ct ce)
        SW.Loop c body -> do 
            Some cle <- lowerExpr c 
            Just Refl <- return $ testEquality SA.StubsBoolRepr (SA.stubsExprToTy cle)
            cb <- lowerStmts body 
            return (SA.Loop cle cb)
        SW.Assignment s e -> do 
            Some cle <- lowerExpr e
            -- lookup s: argument? global? local? new?
            let args = arguments lst 
            let m = List.findIndex (\(SW.Var n _) -> n == s ) args
            case m of 
                Just _ -> do 
                    let fnName = currentFn lst
                    throwError (SPE.ArgumentAssignment fnName s)
                Nothing -> do -- not an argument
                    let globs = globals lst 
                    let m = List.find (\(SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl n _ )) -> n == s) globs
                    case m of 
                        Just (SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl n t)) -> do 
                            return (SA.GlobalAssignment (SA.StubsVar n t) cle)
                        Nothing -> do 
                            let knownVars = inScopeVars lst
                            let m = List.find (\(SW.Var n _) -> n == s) knownVars
                            case m of 
                                Just _ -> return (SA.Assignment (SA.StubsVar s (SA.stubsExprToTy cle) ) cle )
                                Nothing -> do 
                                    -- update state then return
                                    lt <- exprToTy e
                                    let nst = lst{inScopeVars = (SW.Var s lt):knownVars}
                                    put nst
                                    return (SA.Assignment (SA.StubsVar s (SA.stubsExprToTy cle) ) cle )

lowerExprs :: [SW.Expr] -> StubsLowerSM (Some (Ctx.Assignment SA.StubsExpr))
lowerExprs exprs = do 
    foldM (\(Some ctx) e -> do 
            Some ce <- lowerExpr e  
            return$ Some $ Ctx.extend ctx ce) (Some Ctx.empty) exprs 
exprToTy :: SW.Expr -> StubsLowerSM SW.SType 
exprToTy e = do
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
            args <- gets arguments
            let m = List.find (\(SW.Var n _) -> n == v ) args
            case m of 
                Just (SW.Var _ t) -> pure t
                Nothing -> do
                    globs <- gets globals 
                    let m = List.find (\(SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl n _ )) -> n == v) globs
                    case m of 
                        Just (SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl _ t)) -> pure (stubsTyToWeakTy $ Some t) 
                        Nothing -> do 
                            knownVars <- gets inScopeVars
                            let m = List.find (\(SW.Var n _) -> n == v) knownVars
                            case m of 
                                Just (SW.Var _ t) -> pure t
                                Nothing -> do 
                                    fnName <- gets currentFn 
                                    throwError $ SPE.MissingVariable fnName v

-- | Lower a single expression 
-- Calls and Variables are the interesting cases, as we need to lookup return types, and determine if the variable is a global, a local, or a parameter.
lowerExpr :: SW.Expr -> StubsLowerSM (Some SA.StubsExpr)
lowerExpr e = do 
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
            args <- gets arguments
            let m = (List.findIndex (\(SW.Var n _) -> n == v ) args,List.find (\(SW.Var n _) -> n == v ) args)
            case m of 
                (Just i, Just (SW.Var _ t)) -> do 
                    Some st <- lift $ lowerType t
                    return $ Some (SA.ArgLit (SA.StubsArg i st))
                _ -> do -- not an argument, check globals next 
                        globs <- gets globals 
                        let m = List.find (\(SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl n _ )) -> n == v) globs
                        case m of 
                            (Just (SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl n t))) -> do 
                                return $ Some (SA.GlobalVarLit (SA.StubsVar n t))
                            Nothing -> do -- check locals 
                                localVars <- gets inScopeVars
                                let m = List.find (\(SW.Var n _) -> n ==v ) localVars
                                case m of 
                                    Just (SW.Var n t) -> do 
                                        Some st <- lift $ lowerType t
                                        return $ Some (SA.VarLit (SA.StubsVar n st))
                                    Nothing ->  do 
                                        fnName <- gets currentFn 
                                        throwError $ SPE.MissingVariable fnName v
    
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
    
-- | State needed for lowering of functions
data LowerState = LowerState {
    globals :: [SA.SomeStubsGlobalDecl],
    types :: [SA.SomeStubsTyDecl],
    arguments :: [SW.Var],
    inScopeVars :: [SW.Var],
    knownSigs :: [SA.SomeStubsSignature],
    currentFn :: String -- useful for exception handling
}

type StubsParserM = (ExceptT SPE.ParserException IO)
type StubsLowerSM = (StateT LowerState StubsParserM)