module Stubs.Token where
import GHC.Natural (Natural)

data Token = INT 
            | SHORT 
            | LONG 
            | CHAR
            | ULONG 
            | UINT 
            | USHORT 
            | UCHAR
            | UNIT 
            | BOOL 
            | TY -- type keyword 
            | LPAREN 
            | RPAREN 
            | LBRACE 
            | INIT
            | RBRACE 
            | SEMICOLON 
            | COMMA
            | ASSIGNMENT 
            | WHILE 
            | IF 
            | ELSE
            | RETURN
            | AT -- symbol to prefix an intrinsic type, to distinguish from custom/opaque types 
            | FN -- need to disambiguate grammar
            | EXTERN
            | DOT
            | PRIVATE
            | POINTER
            | VAR String 
            | INTLIT Integer 
            | SHORTLIT Integer
            | LONGLIT Integer 
            | CHARLIT Integer 
            | UCHARLIT Natural
            | UINTLIT Natural 
            | USHORTLIT Natural
            | ULONGLIT Natural
            | BOOLLIT Bool
            | UNITLIT
    deriving (Eq, Ord, Show)
            -- should + be a thing or should we stick to functions like internally