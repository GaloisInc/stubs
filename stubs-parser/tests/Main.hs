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
    \fn unit init(){\
    \c=0;\nreturn ();\
    \}"
    let res = SCP.stubsParser input
    let exp = SWA.SModule {SWA.moduleName="", SWA.fns = [SWA.SFn "init" [] SWA.SUnit [SWA.Assignment "c" (SWA.IntLit 0), SWA.Return SWA.UnitLit] ], 
        SWA.tys=[], SWA.globals= [SWA.SGlobalDecl (SWA.Var "c" SWA.SInt)]}
    assertEqual "failed to properly parse" res exp

moduleLowerTest :: TestTree
moduleLowerTest = testCase "can lower a self-contained module" $ do 
    Right res <- runExceptT $ SP.parseStubsOverrides ["./tests/test-data/counter.stb"]
    assertEqual "Some functions not lowered" (length $ SA.fnDecls $ head res) 3 
    assertEqual "Type declaration discarded" (length $ SA.tyDecls $ head res) 1
    assertEqual "Global lost" (length $ SA.globalDecls  $ head res) 1

lowerFailUndeclared :: TestTree 
lowerFailUndeclared = testCase "Should fail with undeclared variable usage" $ do 
    res <- runExceptT $  SP.parseStubsOverrides ["./tests/test-data/broken.stb"]
    case res of 
        Left (SPE.MissingVariable _ _) -> pure ()
        Left _ -> assertFailure "Caught different error"
        Right _ -> assertFailure "Did not catch undeclared variable"

counterClientTest :: TestTree 
counterClientTest = testCase "Successfully compile and lower multiple modules" $ do 
    res <-runExceptT $  SP.parseStubsOverrides ["./tests/test-data/counter.stb", "./tests/test-data/counterClient.stb"]
    case res of 
        Left ex -> assertFailure (show ex)
        Right _ -> pure ()

main :: IO ()
main = defaultMain $ do
    testGroup "Concrete Syntax Tests" [globalDeclTest,fnLexTest,moduleParseTest,moduleLowerTest,lowerFailUndeclared, counterClientTest]