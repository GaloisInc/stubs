{-#LANGUAGE GADTs #-}
{-#LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes#-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}

module Stubs.AST (
    StubsType(..),
    StubsTypeRepr(..),
    StubsStmt(..),
    StubsExpr(..),
    StubsSignature(..),
    SomeStubsSignature(..),
    SomeStubsFunction(..),
    StubsFunction(..),
    StubsArg(..),
    StubsLit(..),
    StubsVar(..),
    StubsLibrary(..),
    StubsProgram(..),
    SomeStubsTyDecl(..),
    StubsTyDecl(..),
    ResolveAlias,
    stubsLibDefs,
    mkStubsLibrary,
    stubsAssignmentToTys,
    stubsExprToTy
    ) where

import Data.Parameterized as P
import Data.Parameterized.Context as Ctx
import Data.Parameterized.TH.GADT
import GHC.TypeLits
import qualified Data.Set as Set

data StubsType where
    StubsInt :: StubsType
    StubsUnit :: StubsType
    StubsBool :: StubsType
    StubsUInt :: StubsType -- unsigned integer
    StubsLong :: StubsType
    StubsShort :: StubsType
    StubsUShort :: StubsType
    StubsULong :: StubsType
    StubsAlias :: Symbol -> StubsType

type StubsInt = 'StubsInt
type StubsUnit = 'StubsUnit
type StubsBool = 'StubsBool
type StubsUInt = 'StubsUInt
type StubsLong = 'StubsLong
type StubsShort = 'StubsShort
type StubsULong = 'StubsULong
type StubsUShort = 'StubsUShort

data StubsTypeRepr a where
    StubsIntRepr :: StubsTypeRepr StubsInt
    StubsUnitRepr :: StubsTypeRepr StubsUnit
    StubsBoolRepr :: StubsTypeRepr StubsBool
    StubsUIntRepr :: StubsTypeRepr StubsUInt
    StubsLongRepr :: StubsTypeRepr StubsLong
    StubsShortRepr :: StubsTypeRepr StubsShort
    StubsULongRepr :: StubsTypeRepr StubsULong
    StubsUShortRepr :: StubsTypeRepr StubsUShort
    StubsAliasRepr :: P.SymbolRepr s -> StubsTypeRepr (ResolveAlias s)

instance ShowF StubsTypeRepr where 
    showF StubsIntRepr = "Int"
    showF StubsUnitRepr = "Unit"
    showF StubsBoolRepr = "Bool"
    showF StubsUIntRepr = "UInt"
    showF StubsLongRepr = "Long"
    showF StubsShortRepr = "Short"
    showF StubsULongRepr = "ULong"
    showF StubsUShortRepr = "UShort"
    showF (StubsAliasRepr s) = "Opaque:" ++ show s 

instance Show (StubsTypeRepr a) where 
    show StubsIntRepr = "Int"
    show StubsUnitRepr = "Unit"
    show StubsBoolRepr = "Bool"
    show StubsUIntRepr = "UInt"
    show StubsLongRepr = "Long"
    show StubsShortRepr = "Short"
    show StubsULongRepr = "ULong"
    show StubsUShortRepr = "UShort"
    show (StubsAliasRepr s) = "Opaque:" ++ show s 

type family ResolveAlias (s :: Symbol) :: StubsType

$(return [])
instance OrdF StubsTypeRepr where
    compareF = $(structuralTypeOrd [t|StubsTypeRepr|]
                   [ (TypeApp (ConType [t|P.SymbolRepr|]) AnyType, [|compareF|]),
                     (TypeApp AnyType AnyType, [|compareF|])
                   , (TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|compareF|]
                     )
                   ]
                  )

instance TestEquality StubsTypeRepr where
    testEquality r1 r2 = case  compareF r1 r2 of
        EQF -> Just Refl
        _ -> Nothing

data StubsStmt where
    Assignment :: StubsVar a -> StubsExpr b -> StubsStmt
    Loop :: StubsExpr StubsBool -> [StubsStmt] -> StubsStmt
    ITE :: StubsExpr StubsBool -> [StubsStmt]-> [StubsStmt]  -> StubsStmt
    Return :: StubsExpr a -> StubsStmt

data StubsSignature (args::Ctx.Ctx StubsType) (ret::StubsType) = StubsSignature {
    sigFnName :: String,
    sigFnArgTys :: Ctx.Assignment StubsTypeRepr args,
    sigFnRetTy :: StubsTypeRepr ret
}

instance Show (StubsSignature args ret) where 
    show (StubsSignature n a r) = n ++ show a ++":"++ show r

data SomeStubsSignature = forall a b . SomeStubsSignature(StubsSignature a b) 

instance Show SomeStubsSignature where 
    show (SomeStubsSignature s) = "Some " ++ show s

instance OrdF (StubsSignature a) where
    compareF s1 s2 = lexCompareF (sigFnRetTy s1) (sigFnRetTy s2) (fromOrdering $ mappend  (compare (sigFnArgTys s1) (sigFnArgTys s2))  (compare (sigFnName s1) (sigFnName s2)))

instance TestEquality (StubsSignature a) where
    testEquality v1 v2 = case compareF v1 v2 of
        EQF -> Just Refl
        _ -> Nothing

instance Eq SomeStubsSignature where
    (==) (SomeStubsSignature (StubsSignature n1 arg1 ret1)) (SomeStubsSignature (StubsSignature n2 arg2 ret2)) = case (compareF arg1 arg2,compareF ret1 ret2, n1==n2) of
        (EQF,EQF,True) -> True
        _ -> False

instance Ord SomeStubsSignature where
    compare s1 s2 = if s1 == s2 then EQ else case (s1,s2) of
        ((SomeStubsSignature (StubsSignature _ args1 ret1)),(SomeStubsSignature (StubsSignature _ args2 ret2))) -> case compareF args1 args2 of 
            EQF -> toOrdering (compareF ret1 ret2)
            LTF -> LT 
            GTF -> GT

data StubsFunction (args::Ctx.Ctx StubsType) (ret::StubsType) = StubsFunction {
    stubFnSig :: StubsSignature args ret,
    stubFnBody :: [StubsStmt]
}
data SomeStubsFunction = forall a b . SomeStubsFunction(StubsFunction a b)

data StubsVar (a::StubsType) = StubsVar {
    varName::String,
    varType::StubsTypeRepr a
}

instance OrdF StubsVar where
    compareF v1 v2 = lexCompareF (varType v1) (varType v2) (fromOrdering (compare (varName v1) (varName v2)))

instance TestEquality StubsVar where
    testEquality v1 v2 = case compareF v1 v2 of
        EQF -> Just Refl
        _ -> Nothing

data StubsArg (a::StubsType) = StubsArg {
    argIdx::Int,
    argType::StubsTypeRepr a
}

instance OrdF StubsArg where
    compareF a1 a2 = lexCompareF (argType a1) (argType a2) (fromOrdering (compare (argIdx a1) (argIdx a2)))

instance TestEquality StubsArg where
    testEquality v1 v2 = case compareF v1 v2 of
        EQF -> Just Refl
        _ -> Nothing

data StubsLit (a::StubsType) where
    IntLit :: Integer -> StubsLit StubsInt
    UnitLit :: StubsLit StubsUnit
    UIntLit :: Natural -> StubsLit StubsUInt
    LongLit :: Integer -> StubsLit StubsLong
    ShortLit :: Integer -> StubsLit StubsShort
    ULongLit :: Natural -> StubsLit StubsULong
    UShortLit :: Natural -> StubsLit StubsUShort
    BoolLit :: Bool -> StubsLit StubsBool


data StubsExpr (a::StubsType) where
    LitExpr :: StubsLit a -> StubsExpr a
    VarLit :: StubsVar a-> StubsExpr a
    ArgLit :: StubsArg a -> StubsExpr a
    --TupleExpr :: Ctx.Assignment StubsExpr ctx -> StubsExpr (StubsTuple ctx)
    AppExpr :: String -> Ctx.Assignment StubsExpr args -> StubsTypeRepr a -> StubsExpr a

$(return [])
instance OrdF StubsLit where
     compareF = $(structuralTypeOrd [t|StubsLit|]
                   [  (TypeApp AnyType AnyType, [|compareF|])
                   , (TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|compareF|]
                     )
                   ]
                  )

instance TestEquality StubsLit where
    testEquality e1 e2 = case compareF e1 e2 of
        EQF -> Just Refl
        _ -> Nothing

instance OrdF StubsExpr where
    compareF = $(structuralTypeOrd [t|StubsExpr|]
                   [  (TypeApp AnyType AnyType, [|compareF|])
                   , (TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|compareF|]
                     )
                   ]
                  )

instance TestEquality StubsExpr where
    testEquality e1 e2 = case compareF e1 e2 of
        EQF -> Just Refl
        _ -> Nothing

data StubsTyDecl s a = StubsTyDecl (P.SymbolRepr s) (StubsTypeRepr a)
data SomeStubsTyDecl = forall s a . SomeStubsTyDecl (StubsTyDecl s a)

data StubsLibrary = StubsLibrary {
    libName :: String,
    fnDecls :: [SomeStubsFunction],
    externSigs :: [SomeStubsSignature],
    tyDecls :: [SomeStubsTyDecl]
}

-- Note: These instances do not give complete equality checking, this is needed for Ord for using a map
instance Eq SomeStubsFunction where
    (==) (SomeStubsFunction (StubsFunction sig1 _)) (SomeStubsFunction (StubsFunction sig2 _)) = (SomeStubsSignature sig1) == (SomeStubsSignature sig2)

instance Eq StubsLibrary where
    (==) a b = case ((fnDecls a) == (fnDecls b), (libName a)== (libName b)) of
        (True,True) -> True
        _ -> False

instance Ord StubsLibrary where
    compare a b = if a == b then EQ else compare (libName a) (libName b)

data StubsProgram = StubsProgram {
    stubsLibs :: [StubsLibrary],
    stubsMain::String
}

stubsExprToTy :: StubsExpr a -> StubsTypeRepr a
stubsExprToTy e = case e of
    LitExpr(IntLit _) ->StubsIntRepr
    LitExpr(BoolLit _) -> StubsBoolRepr
    LitExpr UnitLit -> StubsUnitRepr
    LitExpr(UIntLit _) -> StubsUIntRepr
    LitExpr(LongLit _) -> StubsLongRepr
    LitExpr(ShortLit _) -> StubsShortRepr
    LitExpr(ULongLit _) -> StubsULongRepr
    LitExpr(UShortLit _) -> StubsUShortRepr
    VarLit v -> varType v
    ArgLit a -> argType a
    AppExpr _ _ r -> r

stubsAssignmentToTys :: Ctx.Assignment StubsExpr ctx -> Ctx.Assignment StubsTypeRepr ctx
stubsAssignmentToTys assign = case alist of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend rest elm ->
        Ctx.extend (stubsAssignmentToTys rest) (stubsExprToTy elm)
    where
        alist = Ctx.viewAssign assign

stubsLibDefs :: StubsLibrary -> [SomeStubsSignature]
stubsLibDefs lib = map (\(SomeStubsFunction f) -> SomeStubsSignature (stubFnSig f)) (fnDecls lib)

-- Given a list of functions, generate its external dependencies, for easier library construction
extractLibDeps :: [SomeStubsFunction] -> [SomeStubsSignature]
extractLibDeps fns =
        let int_sigs = Set.fromList $ map (\(SomeStubsFunction(StubsFunction sig _) )-> SomeStubsSignature sig) fns in
            let sigs = Set.fromList $ concatMap (\(SomeStubsFunction (StubsFunction _ stmts)) -> extractSigsStmts stmts) fns in
            (Set.toList $ Set.difference sigs (Set.intersection sigs int_sigs))

extractSigsStmts :: [StubsStmt] -> [SomeStubsSignature]
extractSigsStmts = concatMap (\case
            Assignment _ e -> extractSigExpr e
            Loop cond body -> extractSigExpr cond ++ extractSigsStmts body
            Return e -> extractSigExpr e
            ITE cond t e -> extractSigExpr cond ++ extractSigsStmts t ++ extractSigsStmts e
    )
    where
        extractSigExpr (AppExpr f args ret) = SomeStubsSignature (StubsSignature f (stubsAssignmentToTys args) ret) : extractSigExprs args
        extractSigExpr _ = []

        extractSigExprs :: Ctx.Assignment StubsExpr a -> [SomeStubsSignature]
        extractSigExprs assign = case alist of 
            Ctx.AssignEmpty -> []
            Ctx.AssignExtend a b -> (extractSigExpr b) ++ (extractSigExprs a)
            where alist = Ctx.viewAssign assign

mkStubsLibrary :: String -> [SomeStubsFunction] -> [SomeStubsTyDecl] -> StubsLibrary
mkStubsLibrary name fns tys = StubsLibrary{libName=name,fnDecls=fns,externSigs=extractLibDeps fns,tyDecls=tys}