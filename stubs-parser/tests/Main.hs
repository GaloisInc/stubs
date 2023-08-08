{-#LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Stubs.Lexer as  SL 
import Stubs.Token as ST
import Stubs.ConcreteParser as SCP
import qualified Stubs.WeakAST as SWA
import qualified Stubs.AST as SA
import qualified Stubs.Lower as SLow
import Control.Monad.Except
import qualified Stubs.Parser.Exception as SPE

globalDeclTest :: TestTree 
globalDeclTest = testCase "some global decls" $ do 
    let inp = "bool t\nshort n"
    let tokens = SL.stubsLexer inp
    assertEqual "" tokens [ST.BOOL, ST.VAR "t", ST.SHORT, ST.VAR "n"]

fnLexTest :: TestTree 
fnLexTest = testCase "can scan a function definition" $ do 
    let inp = "int f(int j){ return j }"
    let tokens = SL.stubsLexer inp
    assertEqual "" tokens [ST.INT, ST.VAR "f", ST.LPAREN, ST.INT, ST.VAR "j", ST.RPAREN, ST.LBRACE, ST.RETURN, ST.VAR "j", ST.RBRACE]

moduleParseTest :: TestTree 
moduleParseTest = testCase "can parse a simple module" $ do 
    let input = "int c;\
    \\
    \fn unit init(){\
    \c=0;\nreturn ();\
    \}"
    let res = SCP.stubsParser input
    let exp = SWA.SModule {SWA.moduleName="", SWA.fns = [SWA.SFn "init" [] SWA.SUnit [SWA.Assignment "c" (SWA.IntLit 0), SWA.Return SWA.UnitLit] ], 
        SWA.tys=[], SWA.globals= [SWA.SGlobalDecl (SWA.Var "c" SWA.SInt)]}
    assertEqual "failed to properly parse" res exp

moduleLowerTest :: TestTree
moduleLowerTest = testCase "can lower a self-contained module" $ do 
    input <- SCP.parseFile "./tests/test-data/counter.stb"
    Right res <- runExceptT $ SLow.lowerModule input []
    assertEqual "Some functions not lowered" (length $ SA.fnDecls res) 3 
    assertEqual "Type declaration discarded" (length $ SA.tyDecls res) 1
    assertEqual "Global lost" (length $ SA.globalDecls res) 1
    -- todo : IMPROVE acceptance criteria, equality and show instances missing from lots of AST, so some confidence is lost


lowerFailUndeclared :: TestTree 
lowerFailUndeclared = testCase "Should fail with undeclared variable usage" $ do 
    input <- SCP.parseFile "./tests/test-data/broken.stb"
    res <- runExceptT $ SLow.lowerModule input []
    case res of 
        Left (SPE.MissingVariable _ _) -> pure ()
        Left _ -> assertFailure "Caught different error"
        Right _ -> assertFailure "Did not catch undeclared variable"


main :: IO ()
main = defaultMain $ do
    testGroup "Concrete Syntax Tests" [globalDeclTest,fnLexTest,moduleParseTest,moduleLowerTest,lowerFailUndeclared]