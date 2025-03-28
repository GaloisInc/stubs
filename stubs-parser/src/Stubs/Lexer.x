{
{-#LANGUAGE RankNTypes #-}
-- | A lexer for the Stubs Definition Language, a C-like language.
module Stubs.Lexer(stubsLexer) where

import qualified Data.Text as T
import qualified Data.Text.Read as TR
import qualified Stubs.Token as ST
import GHC.Natural
}

%wrapper "basic"
$alpha = [a-zA-Z]
$digit = [0-9]


tokens :- 
    short                 { token ST.SHORT }
    char                  { token ST.CHAR }
    long                  { token ST.LONG }
    int                   { token ST.INT }
    ushort                { token ST.USHORT }
    ulong                 { token ST.ULONG }
    uchar                 { token ST.UCHAR }
    uint                  { token ST.UINT }
    unit                  { token ST.UNIT }
    bool                  { token ST.BOOL }
    type                  { token ST.TY   }
    if                    { token ST.IF }
    else                  { token ST.ELSE }
    while                 { token ST.WHILE }
    return                { token ST.RETURN }
    fn                    { token ST.FN }
    init                  { token ST.INIT }
    extern                { token ST.EXTERN }
    private               { token ST.PRIVATE}
    pointer               { token ST.POINTER }

    [=]                   { token ST.ASSIGNMENT }
    [\{]                  { token ST.LBRACE }
    [\}]                  { token ST.RBRACE }
    [\;]                  { token ST.SEMICOLON }
    [\(]                  { token ST.LPAREN }
    [\)]                  { token ST.RPAREN }
    [\,]                  { token ST.COMMA }
    [\@]                  { token ST.AT }
    [\.]                  { token ST.DOT }

    true                  { token (ST.BOOLLIT True)}
    false                 { token (ST.BOOLLIT False)}
    [\(][\)]              { token ST.UNITLIT }
    $digit+               { readIntToken ST.INTLIT }
    $digit+U              { readNatToken  ST.UINTLIT }
    $digit+L              { readIntToken ST.LONGLIT }
    $digit+UL             { readNatToken  ST.ULONGLIT }
    $digit+S              { readIntToken ST.SHORTLIT }
    $digit+US             { readNatToken ST.USHORTLIT }

    $digit+C             { readIntToken ST.CHARLIT }
    $digit+UC             { readNatToken ST.UCHARLIT }
    $alpha+               { readStrToken ST.VAR }
    <0> $white+           ;
    [\/][\/](.+)[\n]      ;

{

token :: ST.Token -> (String -> ST.Token)
token t = (\_ -> t)

readToken :: (String -> a ) -> (a -> ST.Token) -> (String -> ST.Token)
readToken rd con = \str -> (con $ rd str)

readIntToken = readToken (\s -> read s :: Integer)
readNatToken = readToken (\s -> read s :: Natural) 
readStrToken = readToken id

stubsLexer=alexScanTokens

}