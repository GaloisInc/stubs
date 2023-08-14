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
import qualified Data.Parameterized.Map as MapF
import Stubs.Arch.X86 ()
import qualified Stubs.Opaque as SO
import qualified Stubs.Translate.Core as STC
import qualified Data.Macaw.CFG as DMC


testEnv = STC.StubsEnv @DMX.X86_64 (DMC.memWidthNatRepr @(DMC.ArchAddrWidth DMX.X86_64)) MapF.empty MapF.empty
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
    p <- ST.translateDecls @DMX.X86_64 ng hAlloc [] [] testEnv MapF.empty [] [SA.SomeStubsFunction fn]
    let cfgs = map fst p 

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
    p <- ST.translateDecls @DMX.X86_64 ng hAlloc [] [] testEnv MapF.empty [] [SA.SomeStubsFunction fn]
    let cfgs = map fst p 

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
    p <- ST.translateDecls @DMX.X86_64 ng hAlloc [] [] testEnv MapF.empty [] [SA.SomeStubsFunction fn]
    let cfgs = map fst p

    -- Expect single CFG
    assertEqual "Unexpected CFG count" 1 (length cfgs)
    LCSC.ACFG _ _ m <- return $ head cfgs

    let blocks = LCCR.cfgBlocks m
    assertEqual "Unexpected Block count" 4 (length blocks) -- While this could be only 3, due to the Generator's implementation 4 blocks are made total

testOpaquenessCheckRet :: TestTree 
testOpaquenessCheckRet = testCase "Catch Opaqueness Violation in return" $ do 
    Some counter <- return $ LCCC.someSymbol "Counter"
    let lib = SA.mkStubsModule "counter" [
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsAliasRepr counter
                    },
                    SA.stubFnBody=[SA.Return $  SA.LitExpr $ SA.IntLit 0]}
            ] [] []
    assertBool "Failed to catch opaqueness violation in return stmt" (not (SO.satOpaque lib))

testOpaquenessCheckArg :: TestTree 
testOpaquenessCheckArg = testCase "Catch Opaqueness Violation in argument" $ do 
    Some counter <- return $ LCCC.someSymbol "Counter"
    let lib = SA.mkStubsModule "counter" [
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="inc",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty (SA.StubsAliasRepr counter),
                    SA.sigFnRetTy=SA.StubsAliasRepr counter
                    },
                    SA.stubFnBody=[SA.Return (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) ) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr )]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="as_int",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty (SA.StubsAliasRepr counter),
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return $ SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)]}
            ] [] []
    assertBool "Failed to catch opaqueness violation in argument" (not (SO.satOpaque lib))

testOpaquenessCheckAssignmentBad :: TestTree 
testOpaquenessCheckAssignmentBad = testCase "Catch Opaqueness Violation in variable assignment" $ do 
    Some counter <- return $ LCCC.someSymbol "Counter"
    let lib = SA.mkStubsModule "counter" [
            SA.SomeStubsFunction SA.StubsFunction {
                SA.stubFnSig = SA.StubsSignature {
                    SA.sigFnName ="inc",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty (SA.StubsAliasRepr counter),
                    SA.sigFnRetTy=SA.StubsIntRepr
                },
                SA.stubFnBody = [SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr) (SA.ArgLit (SA.StubsArg 0 (SA.StubsAliasRepr counter) )), SA.Return $ SA.VarLit (SA.StubsVar "v" SA.StubsIntRepr) ]
        }
         ] [] []
    assertBool "Failed to catch opaqueness violation in variable assignment" (not (SO.satOpaque lib))

testOpaquenessCheckAssignmentOK :: TestTree 
testOpaquenessCheckAssignmentOK = testCase "Allow type changing with decl" $ do 
    Some counter <- return $ LCCC.someSymbol "Counter"
    let lib = SA.mkStubsModule "counter" [
            SA.SomeStubsFunction SA.StubsFunction {
                SA.stubFnSig = SA.StubsSignature {
                    SA.sigFnName ="inc",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty (SA.StubsAliasRepr counter),
                    SA.sigFnRetTy=SA.StubsIntRepr
                },
                SA.stubFnBody = [SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr) (SA.ArgLit (SA.StubsArg 0 (SA.StubsAliasRepr counter) )), SA.Return $ SA.VarLit (SA.StubsVar "v" SA.StubsIntRepr) ]
        }
         ] [SA.SomeStubsTyDecl (SA.StubsTyDecl counter SA.StubsIntRepr)] []
    assertBool "False positive in variable assignment" (SO.satOpaque lib)

main :: IO ()
main = defaultMain $ do
    testGroup "" [testFnTranslationBasic, testFnTranslationITE, testFnTranslationLoop, testOpaquenessCheckRet, testOpaquenessCheckArg, testOpaquenessCheckAssignmentBad, testOpaquenessCheckAssignmentOK]