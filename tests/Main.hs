module Main ( main ) where

import Test.Tasty
import StubsStandaloneTests 
import StubsOverrideTests 

main :: IO ()
main = defaultMain $ do
    testGroup "" $ standaloneTests ++ overrideTests