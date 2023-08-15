{-# LANGUAGE TypeApplications #-}
module ParserOverrideTests(parserTests) where 

import Test.Tasty
import Test.Tasty.HUnit
import qualified Pipeline as STP
import Control.Exception (try)
import qualified Stubs.Translate.Core as STC


genIntegrationTest :: [FilePath] -> FilePath -> [String] -> TestName -> Integer -> TestTree
genIntegrationTest stubs path entries tag exp = testCase tag $ do
    res <- STP.parserCorePipeline path stubs entries
    case res of
        Just n -> assertEqual "Unexpected value returned" exp n
        Nothing -> assertFailure "Failed to get return value"

genIntegrationExceptionTest :: [FilePath] -> FilePath -> [String] -> TestName -> TestTree 
genIntegrationExceptionTest stubs path entries tag = testCase tag $ do 
    t <- try @STC.TranslatorException (STP.parserCorePipeline path stubs entries)
    case t of 
        Left _ -> pure ()
        Right _ -> assertFailure "failed to get expected exception"

counterParsedTest :: TestTree 
counterParsedTest = genIntegrationTest ["./stubs-parser/tests/test-data/counter.stb","./stubs-parser/tests/test-data/counterClient.stb"] "./tests/test-data/multiple_ov.out" ["f","g","j"] "Full integration" 9

initParsedTest :: TestTree 
initParsedTest = genIntegrationTest ["./stubs-parser/tests/test-data/init.stb"] "./tests/test-data/basic.out" ["f"] "Working init hook" 9

externParsedTest :: TestTree 
externParsedTest = genIntegrationTest ["./stubs-parser/tests/test-data/extern.stb"] "./tests/test-data/basic.out" ["f"] "Working override modules" 5

tailRecFactorialTest :: TestTree 
tailRecFactorialTest = genIntegrationTest ["./stubs-parser/tests/test-data/factorial.stb"] "./tests/test-data/basic.out" ["f"] "Tail Recursive Factorial (Concrete)" 120

brokenClockTest :: TestTree 
brokenClockTest = genIntegrationExceptionTest ["./stubs-parser/tests/test-data/privateClock.stb", "./stubs-parser/tests/test-data/brokenClockClient.stb"] "./tests/test-data/basic.out" ["f"] "Private function cannot be invoked"

parserTests = [counterParsedTest, initParsedTest, externParsedTest, tailRecFactorialTest,brokenClockTest]