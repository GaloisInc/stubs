{-#LANGUAGE GADTs #-}
{-#LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes#-}
{-# LANGUAGE TemplateHaskell #-}

module Stubs.AST where
import Data.Parameterized as P
import Data.Parameterized.Context as Ctx
import Data.Parameterized.TH.GADT

data StubsType where
    StubsInt :: StubsType
    StubsUnit :: StubsType
    StubsBool :: StubsType
    --StubsTuple :: Ctx.Ctx StubsType -> StubsType
    StubsAlias :: Symbol -> StubsType -> StubsType

type StubsInt = 'StubsInt
type StubsUnit = 'StubsUnit
type StubsBool = 'StubsBool
--type StubsTuple = 'StubsTuple
type StubsAlias = 'StubsAlias

data StubsTypeRepr a where
    StubsIntRepr :: StubsTypeRepr StubsInt
    StubsUnitRepr :: StubsTypeRepr StubsUnit
    StubsBoolRepr :: StubsTypeRepr StubsBool
    --StubsTupleRepr :: Ctx.Assignment StubsTypeRepr ctx -> StubsTypeRepr (StubsTuple ctx)
    StubsAliasRepr :: P.SymbolRepr s -> StubsTypeRepr a -> StubsTypeRepr a

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
    Assignment :: StubsVar a -> StubsExpr a -> StubsStmt
    Loop :: StubsExpr StubsBool -> [StubsStmt] -> StubsStmt -- When a loop has ITE in it, what happens? Should ITE be a Stmt instead? Would be more C-like
    ITE :: StubsExpr StubsBool -> [StubsStmt]-> [StubsStmt]  -> StubsStmt
    --FunCall :: StubsFunction args ret -> Ctx.Assignment StubsExpr args -> StubsStmt ret
    Return :: StubsExpr a -> StubsStmt

data StubsSignature (args::Ctx.Ctx StubsType) (ret::StubsType) = StubsSignature {
    sigFnName :: String,
    sigFnArgTys :: Ctx.Assignment StubsTypeRepr args,
    sigFnRetTy :: StubsTypeRepr ret
}

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

data StubsExpr (a::StubsType) where
    IntLit :: Integer -> StubsExpr StubsInt
    UnitLit :: StubsExpr StubsUnit
    VarLit :: StubsVar a-> StubsExpr a
    BoolLit :: Bool -> StubsExpr StubsBool
    ArgLit :: StubsArg a -> StubsExpr a
    --TupleExpr :: Ctx.Assignment StubsExpr ctx -> StubsExpr (StubsTuple ctx)
    --AppExpr :: StubsFunction args ret -> Ctx.Assignment StubsExpr args -> StubsExpr ret

$(return [])
instance OrdF StubsExpr where 
    compareF = $(structuralTypeOrd [t|StubsExpr|]
                   [ (TypeApp AnyType AnyType, [|compareF|])
                   , (TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|compareF|]
                     )
                   ]
                  )

instance TestEquality StubsExpr where 
    testEquality e1 e2 = case compareF e1 e2 of 
        EQF -> Just Refl 
        _ -> Nothing

type StubsTyDecl = forall a . String -> StubsTypeRepr a

data StubsProgram = StubsProgram {
    stubsFnDecls :: [SomeStubsFunction],
    stubsTyDecls::[StubsTyDecl],
    stubsMain::String 
}

stubsExprToTy :: StubsExpr a -> StubsTypeRepr a
stubsExprToTy e = case e of 
    IntLit _ -> StubsIntRepr
    BoolLit _ -> StubsBoolRepr
    UnitLit -> StubsUnitRepr
    VarLit v -> varType v
    ArgLit a -> argType a