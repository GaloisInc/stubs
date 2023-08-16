{
module Stubs.ConcreteParser(concreteParser, stubsParser, parseFile) where

import qualified Stubs.Token as ST 
import qualified Stubs.WeakAST as SWA
import qualified Stubs.Lexer as SL
import qualified System.FilePath as SF
}

%name concreteParser 
%tokentype  {ST.Token}
%error {stubsParserError}

%token 
      int   {ST.INT}
      short {ST.SHORT}
      long  {ST.LONG}
      uint  {ST.UINT}
      ushort{ST.USHORT}
      ulong {ST.ULONG}
      bool  {ST.BOOL}
      unit  {ST.UNIT}
      while {ST.WHILE}
      if    {ST.IF}
      else  {ST.ELSE}
      return {ST.RETURN}
      LPAREN { ST.LPAREN }
      RPAREN { ST.RPAREN }
      LBRACE { ST.LBRACE }
      RBRACE { ST.RBRACE }
      COMMA  { ST.COMMA  }
      AT     { ST.AT }
      FN     { ST.FN }
      extern { ST.EXTERN }
      ASSIGN { ST.ASSIGNMENT }
      SEMICOLON   { ST.SEMICOLON }
      INTLIT { ST.INTLIT $$ }
      SHORTLIT { ST.SHORTLIT $$ }
      LONGLIT { ST.LONGLIT $$ }
      UINTLIT { ST.UINTLIT $$ }
      USHORTLIT { ST.USHORTLIT $$ }
      ULONGLIT { ST.ULONGLIT $$ }
      BOOLLIT  { ST.BOOLLIT $$ }
      UNITLIT  { ST.UNITLIT }
      VAR      { ST.VAR $$ }
      TY       {ST.TY}
      INIT     {ST.INIT}
      DOT      { ST.DOT }
      PRIVATE  { ST.PRIVATE }

%% 

Module : ExternDecls TyDecls GlobalDecls Fns {SWA.SModule{SWA.moduleName="", SWA.fns=$4, SWA.tys=$2, SWA.globals=$3, SWA.externs=$1}}

ExternDecl : extern Type VAR UINTLIT SEMICOLON {SWA.SExternDecl{SWA.extName=$3, SWA.extRet=$2, SWA.extParams=[]}}
           | extern Type VAR LPAREN Params RPAREN SEMICOLON {SWA.SExternDecl{SWA.extName=$3, SWA.extRet=$2, SWA.extParams=$5}}

ExternDecls : {- empty -} {[]}
            | ExternDecl {[$1]}
            | ExternDecls ExternDecl {$2 : $1}

Fn : FnMeta FN Type VAR UNITLIT LBRACE Stmts RBRACE {SWA.SFn $4 [] $3 $7 $1} 
   | FnMeta FN Type VAR LPAREN Params RPAREN LBRACE Stmts RBRACE {SWA.SFn $4 $6 $3 $9 $1}

FnMeta : PRIVATE {SWA.FnMetadata False True}
       | PRIVATE INIT {SWA.FnMetadata True True}
       | INIT {SWA.FnMetadata True False}
       | {- empty -} {SWA.FnMetadata False False}
Fns : {- empty -} {[]}
    | Fn {[$1]}
    | Fns Fn {$2 : $1 }

GlobalDecl : Type VAR SEMICOLON {SWA.SGlobalDecl (SWA.Var $2 $1)}
GlobalDecls: {- empty -} {[]}
    | GlobalDecl {[$1]}
    | GlobalDecls GlobalDecl {$1 ++ [$2] }

TyDecl : TY VAR ASSIGN Type SEMICOLON {SWA.STyDecl $2 $4}
TyDecls: {- empty -} {[]}
    | TyDecl {[$1]}
    | TyDecls TyDecl {$2 : $1 }

Type : int {SWA.SInt}
     | short {SWA.SShort}
     | long  {SWA.SLong}
     | uint  {SWA.SUInt}
     | ushort {SWA.SUShort}
     | ulong {SWA.SULong}
     | bool  {SWA.SBool}
     | unit  {SWA.SUnit}
     | VAR {SWA.SCustom $1}
     | AT VAR {SWA.SIntrinsic $2}
     | LPAREN TypeList RPAREN { SWA.STuple $2}

TypeList : Type {[$1]}
          | Type COMMA TypeList {$1 : $3}

Param : Type VAR {SWA.Var $2 $1}
Params : {- empty -} {[]}
       | Param {[$1]}
       | Param COMMA Params {$1 : $3}

Stmt : VAR ASSIGN Expr SEMICOLON {SWA.Assignment $1 $3}
     | return Expr SEMICOLON {SWA.Return $2}
     | while Expr LBRACE Stmts RBRACE {SWA.Loop $2 $4}
     | if Expr LBRACE Stmts RBRACE else LBRACE Stmts RBRACE {SWA.ITE $2 $4 $8}
     | FnCall SEMICOLON {SWA.Assignment "_" $1}
     | Type VAR ASSIGN Expr SEMICOLON {SWA.Declaration $2 $1 $4}

Stmts : {- empty -} {[]}
      | Stmt {[$1]}
      | Stmt Stmts { $1 : $2}

Expr : Literal  { $1 }
     | VAR      { SWA.StVar $1 }
     | FnCall   {$1}
     | Tuple    {$1}
     | TupleAccess  {$1}

FnCall : VAR LPAREN ExprList RPAREN {SWA.Call $1 $3}
     | VAR UNITLIT {SWA.Call $1 []}

Tuple : LPAREN ExprL RPAREN { SWA.TupleExpr $2}

TupleAccess : Tuple DOT INTLIT  {SWA.TupleAccessExpr $1 (fromIntegral $3 )}
            | VAR DOT INTLIT {SWA.TupleAccessExpr (SWA.StVar $1) (fromIntegral $3) }
            | TupleAccess DOT INTLIT {SWA.TupleAccessExpr $1 (fromIntegral $3 )}

Literal : UNITLIT {SWA.UnitLit}
     | BOOLLIT {SWA.BoolLit $1}
     | INTLIT {SWA.IntLit $1}
     | SHORTLIT {SWA.ShortLit $1}
     | LONGLIT {SWA.LongLit $1}
     | UINTLIT {SWA.UIntLit $1}
     | USHORTLIT {SWA.UShortLit $1}
     | ULONGLIT {SWA.ULongLit $1}

ExprList : {- empty -} {[]}
         | ExprL {$1}

ExprL : Expr {[$1]}
       | Expr COMMA ExprList { $1 : $3 } 

{
-- TODO: Improve Error messages
stubsParserError :: [ST.Token] -> a
stubsParserError toks = error $ "Parse error, dumping tokens: " ++ show toks

-- Parse a single module
stubsParser :: String -> SWA.SModule 
stubsParser = concreteParser . SL.stubsLexer 

-- One module per file
parseFile :: FilePath -> IO SWA.SModule 
parseFile path = do
     contents <- readFile path
     let (name, _ ) = SF.splitExtension path
     let m = stubsParser contents 
     return (m{SWA.moduleName= name})
}