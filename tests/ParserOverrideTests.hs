module ParserOverrideTests(parserTests) where 

import Test.Tasty
import Test.Tasty.HUnit
import qualified Pipeline as STP


genIntegrationTest :: [FilePath] -> FilePath -> [String] -> TestName -> Integer -> TestTree
genIntegrationTest stubs path entries tag exp = testCase tag $ do
    res <- STP.parserCorePipeline path stubs entries
    case res of
        Just n -> assertEqual "Unexpected value returned" exp n
        Nothing -> assertFailure "Failed to get return value"


counterParsedTest :: TestTree 
counterParsedTest = genIntegrationTest ["./stubs-parser/tests/test-data/counter.stb","./stubs-parser/tests/test-data/counterClient.stb"] "./tests/test-data/multiple_ov.out" ["f","g","j"] "Full integration" 9

initParsedTest :: TestTree 
initParsedTest = genIntegrationTest ["./stubs-parser/tests/test-data/init.stb"] "./tests/test-data/basic.out" ["f"] "Working init hook" 9

externParsedTest :: TestTree 
externParsedTest = genIntegrationTest ["./stubs-parser/tests/test-data/extern.stb"] "./tests/test-data/basic.out" ["f"] "Working override modules" 5

tailRecFactorialTest :: TestTree 
tailRecFactorialTest = genIntegrationTest ["./stubs-parser/tests/test-data/factorial.stb"] "./tests/test-data/basic.out" ["f"] "Tail Recursive Factorial (Concrete)" 120
parserTests = [counterParsedTest, initParsedTest, externParsedTest, tailRecFactorialTest]