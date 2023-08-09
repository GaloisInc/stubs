{-# LANGUAGE GADTs #-}
module Stubs.Parser.Exception where 
import qualified Stubs.AST as SA
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized (ShowF(showF))

-- | Exception type to use during lowering of WeakAST -> Stubs AST
data ParserException where 
    ArgumentAssignment :: String -> String -> ParserException -- fn name, parameter name
    MissingFunction :: String -> String -> Ctx.Assignment SA.StubsTypeRepr x -> ParserException -- current fn, missing fn
    MissingVariable :: String -> String -> ParserException -- current fn, missing variable

instance Show ParserException where 
    show (ArgumentAssignment fn arg) = "Illegal assignment into argument \"" ++ arg ++ "\" in function " ++ fn
    show (MissingFunction fn c params) = "Call to unknown function \"" ++ c ++ "\" in function " ++ fn ++". Expected Params: " ++  showF params 
    show (MissingVariable fn v) = "Accessing unknown variable \"" ++ v ++ "\" in function " ++ fn