{-#LANGUAGE GADTs #-}
{-#LANGUAGE RankNTypes #-}
{-#LANGUAGE DataKinds #-}
{-#LANGUAGE KindSignatures #-}
{-#LANGUAGE TypeApplications #-}
{-#LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Parameterized.Nonce as PN
import Data.Parameterized.Some
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Stubs.AST as SA
import qualified Data.Parameterized.Context as Ctx
import qualified Stubs.Translate as ST
import qualified Data.Macaw.X86 as DMX
import           Data.Macaw.X86.Symbolic ()
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Data.Parameterized as P
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Data.Parameterized.NatRepr as PN

testFnTranslationBasic :: TestTree
testFnTranslationBasic = testCase "Basic Translation" $ do 
    hAlloc <- LCF.newHandleAllocator
    Some ng <- PN.newIONonceGenerator
    let fn = SA.StubsFunction {
        SA.stubFnName="f",
        SA.stubFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
        SA.stubFnRetTy=SA.StubsIntRepr,
        SA.stubFnBody=[SA.Return (SA.IntLit 20)]
    }
    p <- ST.translateDecls @DMX.X86_64 ng hAlloc [SA.SomeStubsFunction fn]
    let cfgs = LCSC.parsedProgCFGs p 

    -- Expect single CFG
    assertEqual "Unexpected CFG count" (length cfgs) 1
    LCSC.ACFG _ r m <- return $ head cfgs

    -- Expect Int to be BV 64 on X86_64
    Just P.Refl <- return $ P.testEquality r $ LCCC.BVRepr (PN.knownNat @64)
    return ()

main :: IO ()
main = defaultMain $ do
    testGroup "" [testFnTranslationBasic]