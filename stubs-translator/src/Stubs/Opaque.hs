{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

{-|
Description: Opaqueness Enforcement 

This module implements a type-checking pass to ensure that the opaqueness of aliases is properly enforced, as the translation phase cannot do this.  
-}
module Stubs.Opaque(
    satOpaque
) where

import qualified Stubs.AST as SA
import qualified Data.Parameterized as P
import qualified Data.Parameterized.Context as Ctx

-- | Check if module satisifies the opaqueness requirement
satOpaque :: SA.StubsLibrary -> Bool
satOpaque lib = all (opaqueFn (SA.tyDecls lib)) (SA.fnDecls lib)

opaqueFn :: [SA.SomeStubsTyDecl] -> SA.SomeStubsFunction -> Bool
opaqueFn tys (SA.SomeStubsFunction (SA.StubsFunction sig body)) = all (opaqueStmt tys sig) body

symbolLookup :: P.SymbolRepr s -> [SA.SomeStubsTyDecl] -> Maybe SA.SomeStubsTypeRepr
symbolLookup _ [] = Nothing
symbolLookup sy ((SA.SomeStubsTyDecl (SA.StubsTyDecl s ty)):tys) = case P.testEquality s sy of
        Just P.Refl -> Just $ SA.SomeStubsTypeRepr ty
        _ -> symbolLookup sy tys

reifyType :: SA.StubsTypeRepr a -> [SA.SomeStubsTyDecl] -> SA.SomeStubsTypeRepr
reifyType (SA.StubsAliasRepr s) tys = case symbolLookup s tys of
        Just sty -> sty
        Nothing -> SA.SomeStubsTypeRepr (SA.StubsAliasRepr s)
reifyType i _ = SA.SomeStubsTypeRepr i -- only aliases might change 

opaqueStmt :: [SA.SomeStubsTyDecl] -> SA.StubsSignature args ret -> SA.StubsStmt -> Bool
opaqueStmt tys sig (SA.Return e) = reifyType (SA.sigFnRetTy sig) tys == exprToReifyTy e tys && opaqueExpr tys sig e
opaqueStmt tys sig (SA.GlobalAssignment (SA.StubsVar _ vt) e) = reifyType vt tys == exprToReifyTy e tys && opaqueExpr tys sig e 
opaqueStmt tys sig (SA.Assignment (SA.StubsVar _ vt) e) = reifyType vt tys == exprToReifyTy e tys && opaqueExpr tys sig e 
opaqueStmt tys sig (SA.ITE cond t e) = opaqueExpr tys sig cond && all (opaqueStmt tys sig) t && all (opaqueStmt tys sig) e
opaqueStmt tys sig (SA.Loop cond body) = opaqueExpr tys sig cond && all (opaqueStmt tys sig) body

-- mostly to check ArgLit : AppExpr is checked by the translation, as it needs to know signatures separate from the module itself
opaqueExpr :: [SA.SomeStubsTyDecl] -> SA.StubsSignature args ret -> SA.StubsExpr a -> Bool 
opaqueExpr tys sig (SA.ArgLit (SA.StubsArg i t)) = case Ctx.intIndex i (Ctx.size (SA.sigFnArgTys sig)) of
    Nothing -> False 
    Just (P.Some idx) -> reifyType (SA.sigFnArgTys sig Ctx.! idx) tys == reifyType t tys
opaqueExpr _ _ _= True

exprToReifyTy :: SA.StubsExpr a -> [SA.SomeStubsTyDecl] -> SA.SomeStubsTypeRepr
exprToReifyTy (SA.LitExpr l) _ = SA.SomeStubsTypeRepr $ SA.stubsExprToTy (SA.LitExpr l)
exprToReifyTy (SA.VarLit (SA.StubsVar _ t)) tys = reifyType t tys
exprToReifyTy (SA.GlobalVarLit (SA.StubsVar _ t)) tys = reifyType t tys
exprToReifyTy (SA.ArgLit (SA.StubsArg _ t)) tys = reifyType t tys
exprToReifyTy (SA.AppExpr _ _ t) tys = reifyType t tys -- sig itself is checked during translation


