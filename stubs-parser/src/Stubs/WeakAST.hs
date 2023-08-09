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
    SCustom :: String -> SType
    SIntrinsic :: String -> SType
    deriving (Eq,Ord,Show)

data Var = Var String SType
    deriving (Eq,Ord,Show)

data Expr where 
    IntLit :: Integer -> Expr 
    ShortLit :: Integer -> Expr 
    LongLit :: Integer -> Expr 
    UIntLit :: Natural -> Expr 
    UShortLit :: Natural -> Expr
    ULongLit :: Natural -> Expr
    BoolLit :: Bool -> Expr 
    UnitLit :: Expr
    StVar :: String -> Expr 
    Call :: String -> [Expr] -> Expr
    deriving (Eq,Ord,Show)

data Stmt where 
    Assignment :: String -> Expr -> Stmt 
    Return :: Expr -> Stmt 
    Loop :: Expr -> [Stmt] -> Stmt 
    ITE :: Expr -> [Stmt] -> [Stmt] -> Stmt
    deriving (Eq,Ord,Show) 

data SFn = SFn {
    fnName::String,
    fnParams::[Var],
    fnRet :: SType,
    fnBody :: [Stmt],
    isInit :: Bool
}
    deriving (Eq,Ord,Show)
data STyDecl = STyDecl String SType
    deriving (Eq,Ord,Show)
data SGlobalDecl = SGlobalDecl Var
    deriving (Eq,Ord,Show)

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

