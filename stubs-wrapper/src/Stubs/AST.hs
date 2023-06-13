{-#LANGUAGE GADTs #-}
{-#LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes#-}

module Stubs.AST where
import Data.Parameterized as P
import Data.Parameterized.Context as Ctx

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

instance TestEquality StubsTypeRepr where
    testEquality r1 r2 = case (r1,r2) of
        (StubsIntRepr, StubsIntRepr) -> Just Refl
        (StubsBoolRepr, StubsBoolRepr) -> Just Refl
        (StubsUnitRepr, StubsUnitRepr) -> Just Refl
        --(StubsTupleRepr a1, StubsTupleRepr a2) | Just Refl <- testEquality a1 a2 -> Just Refl
        _ -> Nothing

data StubsFunction (args::Ctx.Ctx StubsType) (ret::StubsType) = StubsFunction {
    stubFnName :: String,
    stubFnArgTys :: Ctx.Assignment StubsTypeRepr args,
    stubFnRetTy :: StubsTypeRepr ret,
    stubFnBody :: [StubsStmt]
}
data SomeStubsFunction = forall a b . SomeStubsFunction(StubsFunction a b)

data StubsExpr (a::StubsType) where
    IntLit :: Integer -> StubsExpr StubsInt
    UnitLit :: StubsExpr StubsUnit
    --VarLit :: String -> StubsTypeRepr a -> StubsExpr a
    BoolLit :: Bool -> StubsExpr StubsBool
    --ITE :: StubsExpr StubsBool -> StubsExpr a -> StubsExpr a
    --TupleExpr :: Ctx.Assignment StubsExpr ctx -> StubsExpr (StubsTuple ctx)
    --AppExpr :: StubsFunction args ret -> Ctx.Assignment StubsExpr args -> StubsExpr ret

data StubsStmt where
    --Assignment :: String -> StubsExpr a -> StubsStmt StubsUnit 
    --NoOp :: StubsStmt StubsUnit
    --Seq :: StubsStmt a -> StubsStmt b -> StubsStmt b 
    --Loop :: StubsExpr StubsBool -> StubsStmt StubsUnit -> StubsStmt StubsUnit -- When a loop has ITE in it, what happens? Should ITE be a Stmt instead? Would be more C-like
    --ITE :: StubsExpr StubsBool -> StubsStmt a -> StubsStmt a -> StubsStmt a
    --FunCall :: StubsFunction args ret -> Ctx.Assignment StubsExpr args -> StubsStmt ret
    Return :: StubsExpr a -> StubsStmt

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
    

--funex = FunDecl "f" (Ctx.extend Ctx.empty StubsIntRepr) StubsIntRepr (Return $ IntLit 20)