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
import Lang.Crucible.CFG.Reg as LCCR
import Stubs.Preamble.X86 ()

testFnTranslationBasic :: TestTree
testFnTranslationBasic = testCase "Basic Translation" $ do 
    hAlloc <- LCF.newHandleAllocator
    Some ng <- PN.newIONonceGenerator
    let fn = SA.StubsFunction {
        SA.stubFnSig=SA.StubsSignature{
            SA.sigFnName="f",
            SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
            SA.sigFnRetTy=SA.StubsIntRepr
        },
        SA.stubFnBody=[SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr) (SA.LitExpr $ SA.IntLit 20),SA.Return (SA.LitExpr $ SA.IntLit 20)]
    }
    p <- ST.translateDecls @DMX.X86_64 ng hAlloc [SA.SomeStubsFunction fn]
    let cfgs = ST.crCFGs p 

    -- Expect single CFG
    assertEqual "Unexpected CFG count" (length cfgs) 1
    LCSC.ACFG _ r _ <- return $ head cfgs

    -- Expect Int to be BV 32 on X86_64 -- TODO: make less brittle
    Just P.Refl <- return $ P.testEquality r $ LCCC.BVRepr (PN.knownNat @32) 
    return ()

testFnTranslationITE :: TestTree 
testFnTranslationITE = testCase "ITE Translation" $ do 
    hAlloc <- LCF.newHandleAllocator
    Some ng <- PN.newIONonceGenerator
    let fn = SA.StubsFunction {
        SA.stubFnSig=SA.StubsSignature{
            SA.sigFnName="f",
            SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
            SA.sigFnRetTy=SA.StubsIntRepr
        },
        SA.stubFnBody=[SA.ITE (SA.LitExpr $ SA.BoolLit True) [SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr) (SA.LitExpr $ SA.IntLit 20)] [SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr) (SA.LitExpr $ SA.IntLit 40)],SA.Return (SA.LitExpr $ SA.IntLit 20)]
    }
    p <- ST.translateDecls @DMX.X86_64 ng hAlloc [SA.SomeStubsFunction fn]
    let cfgs = ST.crCFGs p 

    -- Expect single CFG
    assertEqual "Unexpected CFG count" 1 (length cfgs)
    LCSC.ACFG _ _ m <- return $ head cfgs
    
    let blocks = LCCR.cfgBlocks m
    assertEqual "Unexpected Block count" 4 (length blocks)

testFnTranslationLoop :: TestTree 
testFnTranslationLoop = testCase "Loop Translation" $ do 
    hAlloc <- LCF.newHandleAllocator
    Some ng <- PN.newIONonceGenerator
    let fn = SA.StubsFunction {
        SA.stubFnSig=SA.StubsSignature{
            SA.sigFnName="f",
            SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
            SA.sigFnRetTy=SA.StubsIntRepr
        },
        SA.stubFnBody=[SA.Loop (SA.LitExpr $ SA.BoolLit False) [SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr) (SA.LitExpr $ SA.IntLit 40)] ,SA.Return (SA.LitExpr $ SA.IntLit 20)]
    }
    p <- ST.translateDecls @DMX.X86_64 ng hAlloc [SA.SomeStubsFunction fn]
    let cfgs = ST.crCFGs p

    -- Expect single CFG
    assertEqual "Unexpected CFG count" 1 (length cfgs)
    LCSC.ACFG _ _ m <- return $ head cfgs

    let blocks = LCCR.cfgBlocks m
    assertEqual "Unexpected Block count" 4 (length blocks) -- While this could be only 3, due to the Generator's implementation 4 blocks are made total

main :: IO ()
main = defaultMain $ do
    testGroup "" [testFnTranslationBasic, testFnTranslationITE, testFnTranslationLoop]