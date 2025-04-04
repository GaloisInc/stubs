{-# LANGUAGE GADTs #-}
module Stubs.Parser.Exception where 
import qualified Stubs.AST as SA
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized (ShowF(showF))
import qualified Stubs.WeakAST as SW 

-- | Exception type to use during lowering of WeakAST -> Stubs AST
data ParserException where 
    ArgumentAssignment :: String -> String -> ParserException -- fn name, parameter name
    MissingFunction :: String -> String -> Ctx.Assignment SA.StubsTypeRepr x -> ParserException -- current fn, missing fn
    MissingVariable :: String -> String -> ParserException -- current fn, missing variable
    TypeMismatch :: SW.Expr -> SW.SType -> SW.SType -> ParserException -- expected type, actual type
    ExpectedTuple :: SW.SType -> String -> ParserException -- actual type, fn name
    TupleIndexOutOfBounds :: SW.SType -> Int -> ParserException -- tuple type, attempted index

instance Show ParserException where 
    show (ArgumentAssignment fn arg) = "Illegal assignment into argument \"" ++ arg ++ "\" in function " ++ fn
    show (MissingFunction fn c params) = "Call to unknown function \"" ++ c ++ "\" in function " ++ fn ++". Expected Params: " ++  showF params 
    show (MissingVariable fn v) = "Accessing unknown variable \"" ++ v ++ "\" in function " ++ fn
    show (TypeMismatch v t1 t2) = "Type mismatch: expected: " ++ show t1 ++ " got: " ++ show t2 ++ "in expression: " ++ show v
    show (ExpectedTuple ty f) = "Expected tuple, got: " ++ show ty ++ " in " ++ show f
    show (TupleIndexOutOfBounds ty idx) = "Tuple index out of bounds. Type: " ++ show ty ++ " Index: " ++ show idx