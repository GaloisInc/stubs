module Main ( main ) where

import Test.Tasty
import StubsStandaloneTests 
import StubsOverrideTests 
import ParserOverrideTests

main :: IO ()
main = defaultMain $ do
    testGroup "" $ standaloneTests ++ overrideTests ++ parserTests