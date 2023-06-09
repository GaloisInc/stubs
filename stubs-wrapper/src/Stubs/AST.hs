{-#LANGUAGE GADTs #-}
{-#LANGUAGE RankNTypes #-}
{-#LANGUAGE DataKinds #-}
{-#LANGUAGE KindSignatures #-}
{-#LANGUAGE TypeApplications #-}
{-#LANGUAGE OverloadedStrings #-}

module Stubs.AST where 
import Data.Parameterized as P
import Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr as PN
import Lang.Crucible.Types as LCT
import qualified Lang.Crucible.CFG.Expr as LCCE
import qualified Lang.Crucible.CFG.Reg as LCCR

data StubsType where 
    StubsInt :: StubsType 
    StubsUnit :: StubsType
    StubsBool :: StubsType 
    StubsTuple :: Ctx.Ctx StubsType -> StubsType
    StubsAlias :: Symbol -> StubsType -> StubsType

type StubsInt = 'StubsInt
type StubsUnit = 'StubsUnit
type StubsBool = 'StubsBool
type StubsTuple = 'StubsTuple

data StubsTypeRepr a where 
    StubsIntRepr :: StubsTypeRepr StubsInt
    StubsUnitRepr :: StubsTypeRepr StubsUnit
    StubsBoolRepr :: StubsTypeRepr StubsBool
    StubsTupleRepr :: Ctx.Assignment StubsTypeRepr ctx -> StubsTypeRepr (StubsTuple ctx)
    StubsAliasRepr :: P.SymbolRepr s -> StubsTypeRepr a -> StubsTypeRepr a

instance Show (StubsTypeRepr a)

instance ShowF StubsTypeRepr

instance TestEquality StubsTypeRepr where 
    testEquality r1 r2 = case (r1,r2) of 
        (StubsIntRepr, StubsIntRepr) -> Just Refl 
        (StubsBoolRepr, StubsBoolRepr) -> Just Refl 
        (StubsUnitRepr, StubsUnitRepr) -> Just Refl
        (StubsTupleRepr a1, StubsTupleRepr a2) | Just Refl <- testEquality a1 a2 -> Just Refl
        _ -> Nothing

data StubsFunction (args::Ctx.Ctx StubsType) (ret::StubsType) = StubsFunction {
    stubFnName :: String,
    stubFnArgTys :: Ctx.Assignment StubsTypeRepr args,
    stubFnRetTy :: StubsTypeRepr ret
}

data StubsExpr (a::StubsType) where 
    IntLit :: Integer -> StubsExpr StubsInt
    UnitLit :: StubsExpr StubsUnit 
    VarLit :: String -> StubsTypeRepr a -> StubsExpr a
    BoolLit :: Bool -> StubsExpr StubsBool 
    --ITE :: StubsExpr StubsBool -> StubsExpr a -> StubsExpr a
    TupleExpr :: Ctx.Assignment StubsExpr ctx -> StubsExpr (StubsTuple ctx)
    --AppExpr :: Ctx.Assignment StubsExpr args -> StubsFunction args ret -> StubsExpr ret

data StubsStmt a where 
    Assignment :: String -> StubsExpr a -> StubsStmt StubsUnit 
    Seq :: StubsStmt a -> StubsStmt b -> StubsStmt b 
    --Loop :: StubsExpr StubsBool -> StubsStmt a -> StubsStmt StubsUnit -- When a loop has ITE in it, what happens? Should ITE be a Stmt instead? Would be more C-like
    Return :: StubsExpr a -> StubsStmt a 

data StubsDecl where 
    FunDecl :: forall argtys ret . String -> Ctx.Assignment StubsTypeRepr argtys -> StubsTypeRepr ret -> StubsStmt ret -> StubsDecl
    TyDecl :: forall a . String -> StubsTypeRepr a -> StubsDecl  -- Currently only aliasing

type StubsProgram = [StubsDecl]

--funex = FunDecl "f" (Ctx.extend Ctx.empty StubsIntRepr) StubsIntRepr (Return $ IntLit 20)

{-
    Translation to Crucible CFG:
    Step 1: Process all type alias definitions 
    Step 2: Rewrite type alias usages into base types 
    Step 3: Translate function declarations into CFGs

-}

toCrucibleTy :: StubsTypeRepr a -> Some LCT.TypeRepr
toCrucibleTy tyrepr = case tyrepr of 
    StubsIntRepr -> Some $ LCT.BVRepr n
    StubsBoolRepr -> Some $ LCT.BoolRepr
    StubsUnitRepr -> Some LCT.UnitRepr
    StubsTupleRepr ctx -> Some $ LCT.UnitRepr -- todo change
    StubsAliasRepr _ t -> toCrucibleTy t
    where 
        n = PN.knownNat @32 --todo: arch dependent

type AliasMap = [(String, Some StubsTypeRepr)]
collectTyAliases :: [StubsDecl] -> AliasMap -> AliasMap
collectTyAliases ((TyDecl s internal):decls) m = case internal of 
    StubsAliasRepr _ t -> collectTyAliases decls ((s,Some (resolveAlias t)):m)
    _ -> collectTyAliases decls ((s,Some internal):m)
collectTyAliases (_:decls) m = collectTyAliases decls m 
collectTyAliases [] m = m

resolveAlias :: StubsTypeRepr a -> StubsTypeRepr a 
resolveAlias (StubsAliasRepr _ a) = resolveAlias a 
resolveAlias x = x

exprToCrucible :: StubsExpr a -> Some (LCCR.Expr ext s)
exprToCrucible expr = case expr of 
    BoolLit b -> Some $ LCCR.App $ LCCE.BoolLit b
    IntLit i -> Some $ LCCR.App (LCCE.IntegerToBV n (LCCR.App $ LCCE.IntLit i))
    UnitLit -> Some $ LCCR.App LCCE.EmptyApp
    _ -> Some $ LCCR.App $ LCCE.BoolLit True
    where 
         n = PN.knownNat @32

stmtToCrucible stmt = case stmt of 
    Return e -> 
-- appTyCheck :: Ctx.Assignment StubsExpr args -> StubsFunction params ret -> Maybe (StubsExpr ret)
-- appTyCheck args fn = case testEquality (fmapFC typecheck args) (stubFnArgTys fn) of 
--     Just Refl -> Just (AppExpr args fn)
--     Nothing -> Nothing

-- typecheck :: StubsExpr a -> StubsTypeRepr a
-- typecheck expr = error ""

