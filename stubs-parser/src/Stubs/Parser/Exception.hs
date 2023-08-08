{-# LANGUAGE GADTs #-}
module Stubs.Parser.Exception where 

-- | Exception type to use during lowering of WeakAST -> Stubs AST
data ParserException where 
    ArgumentAssignment :: String -> String -> ParserException -- fn name, parameter name
    MissingFunction :: String -> String -> ParserException -- current fn, missing fn
    MissingVariable :: String -> String -> ParserException -- current fn, missing variable

instance Show ParserException where 
    show (ArgumentAssignment fn arg) = "Illegal assignment into argument \"" ++ arg ++ "\" in function " ++ fn
    show (MissingFunction fn c) = "Call to unknown function \"" ++ c ++ "\" in function " ++ fn 
    show (MissingVariable fn v) = "Accessing unknown variable \"" ++ v ++ "\" in function " ++ fn