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
{-|
Description: Core definitions for the Stubs Language's AST

This module contains core definitions for the Stubs Language's AST,
notably the types, reprs, statements, expressions, function definitions, module/library structures, and overall program definition.
Various instances and helper functions for manipulating these types are also present.
-}
module Stubs.AST (
    StubsType(..),
    StubsTypeRepr(..),
    SomeStubsTypeRepr(..),
    StubsStmt(..),
    StubsExpr(..),
    StubsSignature(..),
    SomeStubsSignature(..),
    SomeStubsFunction(..),
    StubsFunction(..),
    StubsArg(..),
    StubsLit(..),
    StubsVar(..),
    CrucibleVar(..),
    StubsModule(..),
    StubsProgram(..),
    SomeStubsTyDecl(..),
    StubsTyDecl(..),
    StubsGlobalDecl(..),
    SomeStubsGlobalDecl(..),
    ResolveAlias,
    ResolveIntrinsic,
    stubsLibDefs,
    mkStubsModule,
    stubsAssignmentToTys,
    stubsExprToTy
    ) where

import Data.Parameterized as P
import Data.Parameterized.Context as Ctx
import Data.Parameterized.TH.GADT
import GHC.TypeLits
import qualified Data.Set as Set
import qualified Lang.Crucible.Types as LCT

-- | The valid types in the Stubs Language 
data StubsType where
    -- | Basic Integer type
    StubsInt :: StubsType 
    StubsUnit :: StubsType
    StubsBool :: StubsType
    -- | Unsigned Integer
    StubsUInt :: StubsType  
    StubsLong :: StubsType
    StubsShort :: StubsType
    StubsUShort :: StubsType
    StubsULong :: StubsType
    -- | Opaque type
    StubsAlias :: Symbol -> StubsType
    -- | Like Crucible Intrinsics: These are known to Override Modules only, and map directly to crucible types
    StubsIntrinsic :: Symbol -> StubsType

type StubsInt = 'StubsInt
type StubsUnit = 'StubsUnit
type StubsBool = 'StubsBool
type StubsUInt = 'StubsUInt
type StubsLong = 'StubsLong
type StubsShort = 'StubsShort
type StubsULong = 'StubsULong
type StubsUShort = 'StubsUShort
type StubsIntrinsic = 'StubsIntrinsic

-- | Value-level type representations of StubsType
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
    StubsIntrinsicRepr :: P.SymbolRepr s -> StubsTypeRepr (StubsIntrinsic s)

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
    showF (StubsIntrinsicRepr s) = "Intrinsic:" ++ show s 

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
    show (StubsIntrinsicRepr s) = "Intrinsic:" ++ show s 

type family ResolveAlias (s :: Symbol) :: StubsType

type family ResolveIntrinsic (s :: Symbol) :: LCT.CrucibleType

data SomeStubsTypeRepr = forall a . SomeStubsTypeRepr (StubsTypeRepr a)

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

instance Eq SomeStubsTypeRepr where 
    (==) (SomeStubsTypeRepr t1) (SomeStubsTypeRepr t2) = case testEquality t1 t2 of 
        Just Refl -> True 
        _ -> False

-- | Statement definitions, such as loops, returns, or variable assignment
data StubsStmt where
    Assignment :: StubsVar a -> StubsExpr b -> StubsStmt
    -- GlobalAssignment translates differently, as global variables are stored differently
    GlobalAssignment :: StubsVar a -> StubsExpr b -> StubsStmt 
    Loop :: StubsExpr StubsBool -> [StubsStmt] -> StubsStmt
    ITE :: StubsExpr StubsBool -> [StubsStmt]-> [StubsStmt]  -> StubsStmt
    Return :: StubsExpr a -> StubsStmt

-- | Stubs Function Signature
data StubsSignature (args::Ctx.Ctx StubsType) (ret::StubsType) = StubsSignature {
    sigFnName :: String,
    sigFnArgTys :: Ctx.Assignment StubsTypeRepr args,
    sigFnRetTy :: StubsTypeRepr ret
}

instance Show (StubsSignature args ret) where 
    show (StubsSignature n a r) = n ++ show a ++":"++ show r

-- | A Signature, with type parameters hidden, allowing a list of signatures with different type parameters
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
        ((SomeStubsSignature (StubsSignature n1 args1 ret1)),(SomeStubsSignature (StubsSignature n2 args2 ret2))) -> case compareF args1 args2 of 
            EQF -> case toOrdering (compareF ret1 ret2) of 
                EQ -> compare n1 n2 
                e -> e
            LTF -> LT 
            GTF -> GT

-- | A Stubs function, consisting of a signature, and a list of statements comprising the body.
data StubsFunction (args::Ctx.Ctx StubsType) (ret::StubsType) = StubsFunction {
    stubFnSig :: StubsSignature args ret,
    stubFnBody :: [StubsStmt]
}

data SomeStubsFunction = forall a b . SomeStubsFunction(StubsFunction a b)

-- | A variable, which has a name, as well as its type, for typechecking.
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

data CrucibleVar (tp::LCT.CrucibleType) = CrucibleVar {
    cvarName::String,
    cvarType::LCT.TypeRepr tp
}

instance OrdF CrucibleVar where
    compareF v1 v2 = lexCompareF (cvarType v1) (cvarType v2) (fromOrdering (compare (cvarName v1) (cvarName v2)))

instance TestEquality CrucibleVar where
    testEquality v1 v2 = case compareF v1 v2 of
        EQF -> Just Refl
        _ -> Nothing

-- | An argument. This includes its type for typechecking, and its index into the signature (checked during translation)
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

-- | Literals in the Stubs Language. These are separate from the expression definition, as each architecture defines a translation for literals.
data StubsLit (a::StubsType) where
    IntLit :: Integer -> StubsLit StubsInt
    UnitLit :: StubsLit StubsUnit
    UIntLit :: Natural -> StubsLit StubsUInt
    LongLit :: Integer -> StubsLit StubsLong
    ShortLit :: Integer -> StubsLit StubsShort
    ULongLit :: Natural -> StubsLit StubsULong
    UShortLit :: Natural -> StubsLit StubsUShort
    BoolLit :: Bool -> StubsLit StubsBool

-- | Expression definition. Note that most interesting code is expressed through function calls, where primitive operations are defined as preamble functions.  
-- See Stubs.Preamble for more on this.
data StubsExpr (a::StubsType) where
    LitExpr :: StubsLit a -> StubsExpr a
    VarLit :: StubsVar a-> StubsExpr a
    GlobalVarLit :: StubsVar a -> StubsExpr a
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

-- | A declaration of an opaque type. During translation this is erased, as a linked program has no concept of opaqueness
data StubsTyDecl s a = StubsTyDecl (P.SymbolRepr s) (StubsTypeRepr a)
-- | A wrapped type declaration. A compilation unit includes a list of these, representing opaque types defined in the module
data SomeStubsTyDecl = forall s a . SomeStubsTyDecl (StubsTyDecl s a)

data StubsGlobalDecl a = StubsGlobalDecl String (StubsTypeRepr a)

data SomeStubsGlobalDecl = forall a . SomeStubsGlobalDecl (StubsGlobalDecl a)

-- | A StubsModule represents a single compilation unit in the Stubs language.
data StubsModule = StubsModule {
    moduleName :: String,
    -- ^ Name for the module
    fnDecls :: [SomeStubsFunction],
    -- ^ Function declarations
    externSigs :: [SomeStubsSignature],
    -- ^ External functions required by the module, necessary for linking 
    tyDecls :: [SomeStubsTyDecl],
    -- ^ Opaque type definitions
    globalDecls :: [SomeStubsGlobalDecl]
    -- ^ Declarations of global data
}

-- Note: These instances do not give complete equality checking, this is needed for Ord for using a map
instance Eq SomeStubsFunction where
    (==) (SomeStubsFunction (StubsFunction sig1 _)) (SomeStubsFunction (StubsFunction sig2 _)) = (SomeStubsSignature sig1) == (SomeStubsSignature sig2)

instance Eq StubsModule where
    (==) a b = case ((fnDecls a) == (fnDecls b), (moduleName a)== (moduleName b)) of
        (True,True) -> True
        _ -> False

instance Ord StubsModule where
    compare a b = if a == b then EQ else compare (moduleName a) (moduleName b)

-- | A complete Stubs program, consisting of several modules,entry points, and initial hook functions
data StubsProgram = StubsProgram {
    stubsModules :: [StubsModule],
    stubsEntryPoints::[String],
    stubsInitFns::[String]
}

-- | Retrieve the type of an expression
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
    GlobalVarLit v -> varType v
    ArgLit a -> argType a
    AppExpr _ _ r -> r

-- | Retrieve types of a list of expressions
stubsAssignmentToTys :: Ctx.Assignment StubsExpr ctx -> Ctx.Assignment StubsTypeRepr ctx
stubsAssignmentToTys assign = case alist of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend rest elm ->
        Ctx.extend (stubsAssignmentToTys rest) (stubsExprToTy elm)
    where
        alist = Ctx.viewAssign assign

-- | Extract signatures for all functions declared in a library
stubsLibDefs :: StubsModule -> [SomeStubsSignature]
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
            GlobalAssignment _ e -> extractSigExpr e
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

-- | Smart constructor for StubsLibrary, which generates the external signature list from the declarations
mkStubsModule :: String -> [SomeStubsFunction] -> [SomeStubsTyDecl] ->  [SomeStubsGlobalDecl] -> StubsModule
mkStubsModule name fns tys globals = StubsModule{moduleName=name,fnDecls=fns,externSigs=extractLibDeps fns,tyDecls=tys, globalDecls=globals}