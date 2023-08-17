{-# LANGUAGE GADTs #-}
module Stubs.WeakAST where 
import GHC.Natural

-- | This module defines a simpler and weaker AST than that used to lower into Crucible.  
-- In essence, this 'Weak' AST is produced by the parser, then transformed into the more precise AST


data SType where 
    SInt :: SType
    SShort :: SType
    SLong :: SType
    SUInt :: SType
    SUShort :: SType
    SULong :: SType
    SUnit :: SType
    SBool :: SType
    SChar :: SType 
    SUChar :: SType
    SPtr :: SType
    SCustom :: String -> SType
    SIntrinsic :: String -> SType
    STuple :: [SType] -> SType
    deriving (Eq,Ord,Show)

-- | Typed Variable
data Var = Var String SType
    deriving (Eq,Ord,Show)


-- | Simple untyped Expressions. Operations like addition are calls, just as internally. 
-- Syntactic Sugar for common binary operations can be done in the parser itself.
data Expr where 
    IntLit :: Integer -> Expr 
    ShortLit :: Integer -> Expr 
    LongLit :: Integer -> Expr 
    UIntLit :: Natural -> Expr 
    UShortLit :: Natural -> Expr
    ULongLit :: Natural -> Expr
    CharLit :: Integer -> Expr 
    UCharLit :: Natural -> Expr 
    BoolLit :: Bool -> Expr 
    UnitLit :: Expr
    StVar :: String -> Expr 
    Call :: String -> [Expr] -> Expr
    TupleExpr :: [Expr] -> Expr
    TupleAccessExpr :: Expr -> Int -> Expr
    deriving (Eq,Ord,Show)

-- | Stmt type corresponding to StubsStmt, with less type enforcement
data Stmt where 
    Assignment :: String -> Expr -> Stmt 
    Return :: Expr -> Stmt 
    Loop :: Expr -> [Stmt] -> Stmt 
    ITE :: Expr -> [Stmt] -> [Stmt] -> Stmt
    Declaration :: String -> SType -> Expr -> Stmt
    deriving (Eq,Ord,Show) 

-- | Collection of non-type info for functions
data FnMetadata = FnMetadata {
    fnInit::Bool,
    fnPrivate::Bool
}
    deriving (Eq,Ord,Show)

data SFn = SFn {
    fnName::String,
    fnParams::[Var],
    fnRet :: SType,
    fnBody :: [Stmt],
    fnMeta :: FnMetadata
}
    deriving (Eq,Ord,Show)
data STyDecl = STyDecl String SType
    deriving (Eq,Ord,Show)
data SGlobalDecl = SGlobalDecl Var
    deriving (Eq,Ord,Show)

-- | Extern declarations allow for type checking of code that may be linked in from OverrideModules (not present in a source file)
data SExternDecl = SExternDecl {
    extName :: String ,
    extRet :: SType , 
    extParams :: [Var]
} deriving (Eq, Ord, Show)

data SModule = SModule {
    moduleName :: String, 
    fns :: [SFn],
    tys :: [STyDecl],
    globals :: [SGlobalDecl],
    externs :: [SExternDecl]
}
    deriving (Eq,Ord,Show)

