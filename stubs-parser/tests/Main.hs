{-#LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Stubs.Lexer as  SL 
import Stubs.Token as ST
import Stubs.ConcreteParser as SCP
import qualified Stubs.WeakAST as SWA
import qualified Stubs.AST as SA
import Control.Monad.Except
import qualified Stubs.Parser.Exception as SPE
import qualified Stubs.Parser as SP

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
    \fn unit initialize(){\
    \c=0;\nreturn ();\
    \}"
    let res = SCP.stubsParser input
    let exp = SWA.SModule {SWA.moduleName="", SWA.fns = [SWA.SFn "initialize" [] SWA.SUnit [SWA.Assignment "c" (SWA.IntLit 0), SWA.Return SWA.UnitLit] $ SWA.FnMetadata False False], 
        SWA.tys=[], SWA.globals= [SWA.SGlobalDecl (SWA.Var "c" SWA.SInt)], SWA.externs=[]}
    assertEqual "failed to properly parse" res exp

moduleLowerTest :: TestTree
moduleLowerTest = testCase "can lower a self-contained module" $ do 
    Right res <- runExceptT $ SP.parseStubsOverrides ["./tests/test-data/counter.stb"] []
    assertEqual "Some functions not lowered" (length $ (SA.fnDecls . head . SA.stubsModules ) res) 3 
    assertEqual "Type declaration discarded" (length $ (SA.tyDecls . head . SA.stubsModules ) res) 1
    assertEqual "Global lost" (length $ (SA.globalDecls  . head . SA.stubsModules ) res) 1

lowerFailUndeclared :: TestTree 
lowerFailUndeclared = testCase "Should fail with undeclared variable usage" $ do 
    res <- runExceptT $  SP.parseStubsOverrides ["./tests/test-data/broken.stb"] ["f"] 
    case res of 
        Left (SPE.MissingVariable _ _) -> pure ()
        Left _ -> assertFailure "Caught different error"
        Right _ -> assertFailure "Did not catch undeclared variable"

parseableTest :: TestName -> [FilePath] -> [String] -> TestTree 
parseableTest tag stubs entries = testCase tag $ do 
    res <- runExceptT $  SP.parseStubsOverrides stubs entries 
    case res of 
        Left ex -> assertFailure (show ex)
        Right _ -> pure ()

counterClientTest :: TestTree 
counterClientTest = parseableTest "Successfully compile and lower multiple modules" ["./tests/test-data/counter.stb", "./tests/test-data/counterClient.stb"] ["f"]

initFnTest :: TestTree 
initFnTest = parseableTest "Successfully parse and lower init hooks" ["./tests/test-data/init.stb"] ["f"]

externDeclTest :: TestTree 
externDeclTest = parseableTest "Successfully parse and lower code with an extern"  ["./tests/test-data/extern.stb"] ["f"]

loopFactorialTest :: TestTree 
loopFactorialTest = parseableTest "Can parse / lower loops"  ["./tests/test-data/loopFactorial.stb"] ["f"]

ifElseChainTest :: TestTree 
ifElseChainTest = parseableTest "Nested if/else" ["./tests/test-data/evenOdd.stb"] ["even", "odd"]

tupParseTest :: TestTree 
tupParseTest = parseableTest "tuple syntax" ["./tests/test-data/tuple.stb"] ["f"]

main :: IO ()
main = defaultMain $ do
    testGroup "Concrete Syntax Tests" [globalDeclTest,fnLexTest,moduleParseTest,moduleLowerTest,lowerFailUndeclared, counterClientTest, initFnTest,externDeclTest,loopFactorialTest,ifElseChainTest,tupParseTest]