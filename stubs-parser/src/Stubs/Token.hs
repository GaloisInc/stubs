module Stubs.Token where
import GHC.Natural (Natural)

data Token = INT 
            | SHORT 
            | LONG 
            | ULONG 
            | UINT 
            | USHORT 
            | UNIT 
            | BOOL 
            | TY -- type keyword 
            | LPAREN 
            | RPAREN 
            | LBRACE 
            | RBRACE 
            | SEMICOLON 
            | COMMA
            | ASSIGNMENT 
            | WHILE 
            | IF 
            | ELSE
            | RETURN
            | AT
            | FN
            | VAR String 
            | INTLIT Integer 
            | SHORTLIT Integer
            | LONGLIT Integer 
            | UINTLIT Natural 
            | USHORTLIT Natural
            | ULONGLIT Natural
            | BOOLLIT Bool
            | UNITLIT
    deriving (Eq, Ord, Show)
            -- should + be a thing or should we stick to functions like internally