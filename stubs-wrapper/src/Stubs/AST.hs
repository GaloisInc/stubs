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
import GHC.TypeLits

data StubsType where
    StubsInt :: StubsType
    StubsUnit :: StubsType
    StubsBool :: StubsType
    StubsUInt :: StubsType -- unsigned integer
    StubsLong :: StubsType
    StubsShort :: StubsType
    StubsAlias :: Symbol -> StubsType -> StubsType

type StubsInt = 'StubsInt
type StubsUnit = 'StubsUnit
type StubsBool = 'StubsBool
type StubsUInt = 'StubsUInt
type StubsLong = 'StubsLong
type StubsShort = 'StubsShort
type StubsAlias = 'StubsAlias


data StubsTypeRepr a where
    StubsIntRepr :: StubsTypeRepr StubsInt
    StubsUnitRepr :: StubsTypeRepr StubsUnit
    StubsBoolRepr :: StubsTypeRepr StubsBool
    StubsUIntRepr :: StubsTypeRepr StubsUInt
    StubsLongRepr :: StubsTypeRepr StubsLong
    StubsShortRepr :: StubsTypeRepr StubsShort
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
    Loop :: StubsExpr StubsBool -> [StubsStmt] -> StubsStmt
    ITE :: StubsExpr StubsBool -> [StubsStmt]-> [StubsStmt]  -> StubsStmt
    Return :: StubsExpr a -> StubsStmt

data StubsSignature (args::Ctx.Ctx StubsType) (ret::StubsType) = StubsSignature {
    sigFnName :: String,
    sigFnArgTys :: Ctx.Assignment StubsTypeRepr args,
    sigFnRetTy :: StubsTypeRepr ret
}

data SomeStubsSignature = forall a b . SomeStubsSignature(StubsSignature a b)

instance OrdF (StubsSignature a) where 
    compareF s1 s2 = lexCompareF (sigFnRetTy s1) (sigFnRetTy s2) (fromOrdering $ mappend  (compare (sigFnArgTys s1) (sigFnArgTys s2))  (compare (sigFnName s1) (sigFnName s2)))

instance TestEquality (StubsSignature a) where 
    testEquality v1 v2 = case compareF v1 v2 of 
        EQF -> Just Refl 
        _ -> Nothing


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

type StubsTyDecl = forall a . String -> StubsTypeRepr a

data StubsProgram = StubsProgram {
    stubsFnDecls :: [SomeStubsFunction],
    stubsTyDecls::[StubsTyDecl],
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