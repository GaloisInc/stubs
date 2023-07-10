{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Main ( main ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Stubs.Solver as S
import Stubs.EntryPoint as SE
import qualified Stubs.Memory as SM
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Data.Parameterized.Nonce as PN
import Data.Parameterized.Some
import qualified Lang.Crucible.Backend as LCB
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.BitVector.Sized as BV
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.RegMap (RegEntry(regValue))
import Control.Lens
import What4.Interface (asConcrete)
import What4.Concrete (fromConcreteBV)
import Infrastructure as SI
import qualified Data.Parameterized.Context.Unsafe as Ctx
import Stubs.AST as SA
import qualified Stubs.Translate as ST

import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified Data.Macaw.X86 as DMX
import qualified Data.List as List
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.CFG.SSAConversion as LCSSA
import qualified What4.Interface as WI
import qualified Lang.Crucible.Simulator as LCSE
import qualified Stubs.Preamble as SPR
import Stubs.Preamble.X86 () --for instance
import Data.Parameterized.SymbolRepr (someSymbol)

smallPipeline :: forall arch args ret ext p. (DMS.SymArchConstraints arch, ext ~ DMS.MacawExt arch, p ~ (), SPR.Preamble arch) =>
                                        ST.CrucibleProgram arch ->
                                        LCCC.SomeCFG (DMS.MacawExt arch) args ret ->
                                        (forall sym . sym -> Ctx.Assignment LCT.TypeRepr args -> IO (Ctx.Assignment (LCS.RegEntry sym) args)) ->
                                        LCT.TypeRepr ret->
                                        (forall sym . WI.IsExprBuilder sym => (LCSE.ExecResult p sym ext (LCS.RegEntry sym ret)) -> IO Bool) ->
                                        IO Bool
smallPipeline prog cfg argsf ret check = do
    hAlloc <- LCF.newHandleAllocator
    let pinst = ProgramInstance{ piPath="",
                                 piBinary="",
                                 piFsRoot=Nothing,
                                 piCommandLineArguments=[],
                                 piConcreteEnvVars=[],
                                 piConcreteEnvVarsFromBytes=[],
                                 piSymbolicEnvVars=[],
                                 piSolver=S.Z3,
                                 piFloatMode=S.IEEE,
                                 piEntryPoint=SE.DefaultEntryPoint,
                                 piMemoryModel=SM.DefaultMemoryModel,
                                 piOverrideDir=Nothing,
                                 piIterationBound=Nothing,
                                 piRecursionBound=Nothing,
                                 piSolverInteractionFile=Nothing,
                                 piSharedObjectDir=Nothing,
                                 piLogSymbolicBranches=Nothing,
                                 piLogFunctionCalls=Nothing
                                 }
    Some ng <- PN.newIONonceGenerator
    S.withOnlineSolver (piSolver pinst) (piFloatMode pinst) ng $ \bak -> do
        let sym = LCB.backendGetSym bak

        LCCC.SomeCFG unwrappedCfg <- return cfg
        args <- argsf sym (LCCC.cfgArgTypes unwrappedCfg)

        SI.symexec bak hAlloc prog cfg args ret check

testProg :: StubsProgram
testProg =
    let fn = SA.StubsFunction {
        SA.stubFnSig=SA.StubsSignature{
            SA.sigFnName="f",
            SA.sigFnArgTys=Ctx.empty,
            SA.sigFnRetTy=SA.StubsIntRepr
        },
        SA.stubFnBody=[SA.Return $ SA.AppExpr "g" (Ctx.extend Ctx.empty $ SA.LitExpr $ SA.IntLit 20) SA.StubsIntRepr]
    } in let int_fun = SA.StubsFunction {
        SA.stubFnSig=SA.StubsSignature{
            SA.sigFnName="g",
            SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
            SA.sigFnRetTy=SA.StubsIntRepr
        },
        SA.stubFnBody=[SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr)  (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)), SA.Return (SA.VarLit (SA.StubsVar "v" SA.StubsIntRepr))]
    } in SA.StubsProgram {
        SA.stubsEntryPoints=["f"],
        SA.stubsLibs=[SA.StubsLibrary{
            SA.fnDecls=[SA.SomeStubsFunction fn, SA.SomeStubsFunction int_fun],
            SA.externSigs=[],
            SA.libName="",
            SA.tyDecls=[],
            SA.globalDecls=[]
        }]
    }

linkerTest :: TestTree
linkerTest = genTestCase ( SA.StubsProgram {
        SA.stubsLibs=[SA.StubsLibrary{
            SA.fnDecls = [
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "main" Ctx.empty SA.StubsIntRepr) [SA.Return (SA.AppExpr "double" (Ctx.extend Ctx.empty (SA.LitExpr $ SA.IntLit 5)) SA.StubsIntRepr)] ),
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "double" (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) [SA.Return (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) SA.StubsIntRepr)])
        ],
            SA.externSigs=[],
            SA.libName="",
            SA.tyDecls=[],
            SA.globalDecls=[]
        }],
        SA.stubsEntryPoints = ["main"]
    }) check "Can link preamble into stub"
    where
        check :: (forall sym . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult p sym ext (LCS.RegEntry sym ret) -> IO Bool)
        check retRepr crucibleRes = case crucibleRes of
                FinishedResult _ r -> case r of
                                        TotalRes v -> do
                                            let q = view gpValue v
                                            case retRepr of
                                                LCT.BVRepr _ -> case asConcrete $ regValue q of
                                                    Just k -> if BV.asUnsigned (fromConcreteBV k) == 10 then return True else print "Unexpected value received" >> return False
                                                    Nothing -> print "Failed to concretize return" >> return False
                                                _ -> print "Unexpected return type" >> return False
                                        _ -> print "Failed to get complete result" >> return False
                _ -> print "Failed to finish execution" >> return False

factorialTest :: TestTree
factorialTest = genTestCase (SA.StubsProgram {
        SA.stubsLibs=[SA.StubsLibrary{
            SA.fnDecls = [
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "main" Ctx.empty SA.StubsIntRepr) [SA.Return (SA.AppExpr "factorial" (Ctx.extend (Ctx.extend Ctx.empty (SA.LitExpr $ SA.IntLit 5)) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr)] ),
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "factorial" (Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) SA.StubsIntRepr)
            [SA.ITE (SA.AppExpr "gt" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.LitExpr $ SA.IntLit 0) ) SA.StubsBoolRepr)
            [SA.Return (SA.AppExpr "factorial"  (Ctx.extend (Ctx.extend Ctx.empty (SA.AppExpr "minus" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) ) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr ) ) (SA.AppExpr "mult" (Ctx.extend (Ctx.extend Ctx.empty  (SA.ArgLit (SA.StubsArg 1 SA.StubsIntRepr)))  (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) ) SA.StubsIntRepr   )  )  SA.StubsIntRepr)   ]
            [(SA.Return (SA.ArgLit (SA.StubsArg 1 SA.StubsIntRepr)) )] ])
        ],
        SA.externSigs = [],
        SA.libName="",
        SA.tyDecls=[],
        SA.globalDecls=[]
        }],
        SA.stubsEntryPoints = ["main"]
    }) check "calculates factorial of 5"
    where
        check :: (forall sym . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult p sym ext (LCS.RegEntry sym ret) -> IO Bool)
        check retRepr crucibleRes = case crucibleRes of
                FinishedResult _ r -> case r of
                                        TotalRes v -> do
                                            let q = view gpValue v
                                            case retRepr of
                                                LCT.BVRepr _ -> case asConcrete $ regValue q of
                                                    Just k -> if BV.asUnsigned (fromConcreteBV k) == 120 then return True else print "Unexpected value received" >> return False
                                                    Nothing -> print "Failed to concretize return" >> return False
                                                _ -> print "Unexpected return type" >> return False
                                        _ -> print "Failed to get complete result" >> return False
                _ -> print "Failed to finish execution" >> return False

symExecTest :: TestTree
symExecTest = genTestCase testProg check "Symbolic Execution smoke test"
    where
        check :: (forall sym . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult p sym ext (LCS.RegEntry sym ret) -> IO Bool)
        check retRepr crucibleRes = case crucibleRes of
                FinishedResult _ r -> case r of
                                        TotalRes v -> do
                                            let q = view gpValue v
                                            case retRepr of
                                                LCT.BVRepr _ -> case asConcrete $ regValue q of
                                                    Just k -> if BV.asUnsigned (fromConcreteBV k) == 20 then return True else print "Unexpected value received" >> return False
                                                    Nothing -> print "Failed to concretize return" >> return False
                                                _ -> print "Unexpected return type" >> return False
                                        _ -> print "Failed to get complete result" >> return False
                _ -> print "Failed to finish execution" >> return False

moduleTest :: TestTree
moduleTest = genTestCase SA.StubsProgram{
    SA.stubsEntryPoints=["f"],
    SA.stubsLibs=[
        SA.mkStubsLibrary "core" [SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="f",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return $ SA.AppExpr "g" (Ctx.extend Ctx.empty $ SA.LitExpr $ SA.IntLit 20) SA.StubsIntRepr]}] [] [],
        SA.mkStubsLibrary "internal" [SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="g",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                    SA.sigFnRetTy=SA.StubsIntRepr
                },
            SA.stubFnBody=[SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr)  (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)), SA.Return (SA.VarLit (SA.StubsVar "v" SA.StubsIntRepr))]
            }] [] []
     ]
} check "Module Test"
    where
        check :: (forall sym . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult p sym ext (LCS.RegEntry sym ret) -> IO Bool)
        check retRepr crucibleRes = case crucibleRes of
                FinishedResult _ r -> case r of
                                        TotalRes v -> do
                                            let q = view gpValue v
                                            case retRepr of
                                                LCT.BVRepr _ -> case asConcrete $ regValue q of
                                                    Just k -> if BV.asUnsigned (fromConcreteBV k) == 20 then return True else print "Unexpected value received" >> return False
                                                    Nothing -> print "Failed to concretize return" >> return False
                                                _ -> print "Unexpected return type" >> return False
                                        _ -> print "Failed to get complete result" >> return False
                _ -> print "Failed to finish execution" >> return False

opaqueTest :: TestTree
opaqueTest = genTestCaseIO ( do
        Some counter <- return $ someSymbol "Counter"
        return SA.StubsProgram {
        SA.stubsEntryPoints=["main"],
        SA.stubsLibs=[
            SA.mkStubsLibrary "counter" [
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=(SA.StubsAliasRepr counter)
                    },
                    SA.stubFnBody=[SA.Return $  SA.LitExpr $ SA.IntLit 0]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="inc",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty (SA.StubsAliasRepr counter),
                    SA.sigFnRetTy=(SA.StubsAliasRepr counter)
                    },
                    SA.stubFnBody=[SA.Return (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) ) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr )]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="as_int",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty (SA.StubsAliasRepr counter),
                    SA.sigFnRetTy=(SA.StubsIntRepr)
                    },
                    SA.stubFnBody=[SA.Return $ SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)]}
        ] [SA.SomeStubsTyDecl (SA.StubsTyDecl counter SA.StubsIntRepr)] [],
            SA.mkStubsLibrary "core" [
                SA.SomeStubsFunction
                    SA.StubsFunction {
                        SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="main",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return (SA.AppExpr "as_int" (Ctx.extend Ctx.empty (SA.AppExpr "inc" (Ctx.extend Ctx.empty (SA.AppExpr "init" Ctx.empty (SA.StubsAliasRepr counter))) (SA.StubsAliasRepr counter))) SA.StubsIntRepr)]
                    }
            ] [] []
        ]   }) check "Opaque Test"
    where
        check :: (forall sym . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult p sym ext (LCS.RegEntry sym ret) -> IO Bool)
        check retRepr crucibleRes = case crucibleRes of
                FinishedResult _ r -> case r of
                                        TotalRes v -> do
                                            let q = view gpValue v
                                            case retRepr of
                                                LCT.BVRepr _ -> case asConcrete $ regValue q of
                                                    Just k -> if BV.asUnsigned (fromConcreteBV k) == 1 then return True else print "Unexpected value received" >> return False
                                                    Nothing -> print "Failed to concretize return" >> return False
                                                _ -> print "Unexpected return type" >> return False
                                        _ -> print "Failed to get complete result" >> return False
                AbortedResult _ (AbortedExec r _) -> print ("Aborted Execution:" ++ show r) >> return False
                _ -> print "Failed to finish execution" >> return False

globalVarTest :: TestTree
globalVarTest = genTestCase SA.StubsProgram{
        SA.stubsEntryPoints= ["main"],
        SA.stubsLibs = [
            SA.mkStubsLibrary "internal" [
                SA.SomeStubsFunction (
                    SA.StubsFunction{
                        SA.stubFnSig=SA.StubsSignature{
                            SA.sigFnName="set",
                            SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                            SA.sigFnRetTy=SA.StubsUnitRepr
                        },
                        SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) , SA.Return $ SA.LitExpr SA.UnitLit]
                    }
                )

            ] [] [SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl "i" SA.StubsIntRepr)],
            SA.mkStubsLibrary "core" [
                SA.SomeStubsFunction (
                    SA.StubsFunction{
                        SA.stubFnSig=SA.StubsSignature{
                            SA.sigFnName="main",
                            SA.sigFnArgTys=Ctx.empty,
                            SA.sigFnRetTy=SA.StubsIntRepr
                        },
                        SA.stubFnBody=[SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "set" (Ctx.extend Ctx.empty (SA.LitExpr $ SA.IntLit 5) ) SA.StubsUnitRepr), SA.Return $ SA.GlobalVarLit $ SA.StubsVar "i" SA.StubsIntRepr]
                    }
                )
            ] [] []
        ]
    } check "Basic Global Variable functionality"
    where
        check :: (forall sym . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult p sym ext (LCS.RegEntry sym ret) -> IO Bool)
        check retRepr crucibleRes = case crucibleRes of
                FinishedResult _ r -> case r of
                                        TotalRes v -> do
                                            let q = view gpValue v
                                            case retRepr of
                                                LCT.BVRepr _ -> case asConcrete $ regValue q of
                                                    Just k -> if BV.asUnsigned (fromConcreteBV k) == 5 then return True else print "Unexpected value received" >> return False
                                                    Nothing -> print "Failed to concretize return" >> return False
                                                _ -> print "Unexpected return type" >> return False
                                        _ -> print "Failed to get complete result" >> return False
                AbortedResult _ (AbortedExec r _) -> print ("Aborted Execution:" ++ show r) >> return False
                _ -> print "Failed to finish execution" >> return False


opaqueGlobalTest :: TestTree
opaqueGlobalTest = genTestCaseIO (do
        Some counter <- return $ someSymbol "Counter"
        return SA.StubsProgram {
            SA.stubsEntryPoints=["main"],
            SA.stubsLibs=[
                SA.mkStubsLibrary "counter" [
                    SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsUnitRepr
                    },
                    SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.LitExpr $ SA.IntLit 0),SA.Return $  SA.LitExpr $ SA.UnitLit]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="inc",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsUnitRepr
                    },
                    SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.GlobalVarLit $ SA.StubsVar "i" SA.StubsIntRepr) ) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr),SA.Return $  SA.LitExpr SA.UnitLit]},

            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="get",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return $ SA.GlobalVarLit $ SA.StubsVar "i" SA.StubsIntRepr]}

                ] [SA.SomeStubsTyDecl (SA.StubsTyDecl counter SA.StubsIntRepr)] [SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl "i" (SA.StubsAliasRepr counter))],
                SA.mkStubsLibrary "core"  [
                    SA.SomeStubsFunction (
                    SA.StubsFunction{
                        SA.stubFnSig=SA.StubsSignature{
                            SA.sigFnName="main",
                            SA.sigFnArgTys=Ctx.empty,
                            SA.sigFnRetTy=SA.StubsIntRepr
                        },
                        SA.stubFnBody=[SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "init" Ctx.empty SA.StubsUnitRepr),SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr), SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr),SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr), SA.Return (SA.AppExpr "get" Ctx.empty SA.StubsIntRepr)]
                    }
                )
                ]
                [] []
            ]
            }
            ) check "Opaque Global Variable Functionality"
     where
        check :: (forall sym . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult p sym ext (LCS.RegEntry sym ret) -> IO Bool)
        check retRepr crucibleRes = case crucibleRes of
                FinishedResult _ r -> case r of
                                        TotalRes v -> do
                                            let q = view gpValue v
                                            case retRepr of
                                                LCT.BVRepr _ -> case asConcrete $ regValue q of
                                                    Just k -> if BV.asUnsigned (fromConcreteBV k) == 3 then return True else print ("Unexpected value received: " ++ show (BV.asUnsigned (fromConcreteBV k))) >> return False
                                                    Nothing -> print "Failed to concretize return" >> return False
                                                _ -> print "Unexpected return type" >> return False
                                        _ -> print "Failed to get complete result" >> return False
                AbortedResult _ (AbortedExec r _) -> print ("Aborted Execution:" ++ show r) >> return False
                _ -> print "Failed to finish execution" >> return False


genTestCaseIO :: IO StubsProgram -> (forall sym ret . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult () sym (DMS.MacawExt DMX.X86_64) (LCS.RegEntry sym ret) -> IO Bool) -> TestName -> TestTree
genTestCaseIO iprog check tag = testCase tag $ do
    Some ng <- PN.newIONonceGenerator
    hAlloc <- LCF.newHandleAllocator
    sprog <- iprog
    cprog <- ST.translateProgram @DMX.X86_64 ng hAlloc sprog
    let prog = head cprog
    case lookupEntry (ST.crEntry prog) (ST.crCFGs prog) of
        Nothing -> assertFailure "Translate produced invalid program: no cfg for entry point"
        Just (LCSC.ACFG _ ret icfg) -> do
            res <- smallPipeline prog ( LCSSA.toSSA icfg) f ret (check ret)
            if res then assertBool "" True else assertFailure "Test failed"
    where
        lookupEntry e = List.find (\(LCSC.ACFG _ _ cfg)-> show (LCF.handleName $ LCCR.cfgHandle cfg) == e)
        f :: (forall sym . sym -> Ctx.Assignment LCT.TypeRepr args -> IO (Ctx.Assignment (LCS.RegEntry sym) args))
        f _ assign = case Ctx.viewAssign assign of
            Ctx.AssignEmpty -> return Ctx.empty
            _ -> error "Irrelevant to test"

genTestCase :: StubsProgram ->  (forall sym ret . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult () sym (DMS.MacawExt DMX.X86_64) (LCS.RegEntry sym ret) -> IO Bool) -> TestName -> TestTree
genTestCase sprog check tag = testCase tag $ do
    Some ng <- PN.newIONonceGenerator
    hAlloc <- LCF.newHandleAllocator
    cprog <- ST.translateProgram @DMX.X86_64 ng hAlloc sprog
    let prog = head cprog
    case lookupEntry (ST.crEntry prog) (ST.crCFGs prog) of
        Nothing -> assertFailure "Translate produced invalid program: no cfg for entry point"
        Just (LCSC.ACFG _ ret icfg) -> do
            res <- smallPipeline prog ( LCSSA.toSSA icfg) f ret (check ret)
            if res then assertBool "" True else assertFailure "Test failed"
    where
        lookupEntry e = List.find (\(LCSC.ACFG _ _ cfg)-> show (LCF.handleName $ LCCR.cfgHandle cfg) == e)
        f :: (forall sym . sym -> Ctx.Assignment LCT.TypeRepr args -> IO (Ctx.Assignment (LCS.RegEntry sym) args))
        f _ assign = case Ctx.viewAssign assign of
            Ctx.AssignEmpty -> return Ctx.empty
            _ -> error "Irrelevant to test"

corePipelinePreambleTest :: TestTree 
corePipelinePreambleTest = testCase "Core Pipeline Preamble Check" $ do 
    i <- corePipeline "./tests/test-data/a.out" sProgs
    case i of 
        Just n -> assertEqual "Unexpected value returned" n 20
        Nothing -> assertFailure "Failed to get return value"
    where 
        sProgs =  [SA.StubsProgram {
    SA.stubsEntryPoints=["f"],
    SA.stubsLibs=[SA.mkStubsLibrary "core" [
        SA.SomeStubsFunction SA.StubsFunction{
            SA.stubFnSig= SA.StubsSignature{
                SA.sigFnName="f",
                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                SA.sigFnRetTy=SA.StubsIntRepr
            },
            SA.stubFnBody=[SA.Return (SA.AppExpr "mult" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.LitExpr $ SA.IntLit 4))  SA.StubsIntRepr)]
        }
    ] [] []]
}]

corePipelineModuleTest :: TestTree 
corePipelineModuleTest = testCase "Core Pipeline Module Check" $ do 
    i <- corePipeline "./tests/test-data/a.out" sProgs
    case i of 
        Just n -> assertEqual "Unexpected value returned" n 20
        Nothing -> assertFailure "Failed to get return value"
    where 
        sProgs =  [SA.StubsProgram {
    SA.stubsEntryPoints=["f"],
    SA.stubsLibs=[SA.mkStubsLibrary "core" [
        SA.SomeStubsFunction SA.StubsFunction{
            SA.stubFnSig= SA.StubsSignature{
                SA.sigFnName="f",
                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                SA.sigFnRetTy=SA.StubsIntRepr
            },
            SA.stubFnBody=[SA.Return (SA.AppExpr "g" (Ctx.extend  Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)))  SA.StubsIntRepr)]
        }
    ] [] [],
    SA.mkStubsLibrary "internal" [
        SA.SomeStubsFunction SA.StubsFunction{
            SA.stubFnSig= SA.StubsSignature{
                SA.sigFnName="g",
                SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                SA.sigFnRetTy=SA.StubsIntRepr
            },
            SA.stubFnBody=[SA.Return (SA.AppExpr "mult" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.LitExpr $ SA.IntLit 4))  SA.StubsIntRepr)]
        }
    ] [] []
    ]
}]
    
corePipelineOpaqueTest :: TestTree 
corePipelineOpaqueTest = genCoreTestIO (do 
        Some counter <- return $ someSymbol "Counter"
        return [SA.StubsProgram {
        SA.stubsEntryPoints=["f"],
        SA.stubsLibs=[
            SA.mkStubsLibrary "counter" [
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=(SA.StubsAliasRepr counter)
                    },
                    SA.stubFnBody=[SA.Return $  SA.LitExpr $ SA.IntLit 0]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="inc",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty (SA.StubsAliasRepr counter),
                    SA.sigFnRetTy=(SA.StubsAliasRepr counter)
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
        ] [SA.SomeStubsTyDecl (SA.StubsTyDecl counter SA.StubsIntRepr)] [],
            SA.mkStubsLibrary "core" [
                SA.SomeStubsFunction
                    SA.StubsFunction {
                        SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="f",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return (SA.AppExpr "as_int" (Ctx.extend Ctx.empty (SA.AppExpr "inc" (Ctx.extend Ctx.empty (SA.AppExpr "init" Ctx.empty (SA.StubsAliasRepr counter))) (SA.StubsAliasRepr counter))) SA.StubsIntRepr)]
                    }
            ] [] []
        ]   }]
    ) "./tests/test-data/a.out" "Core Pipeline Opaque Check" 1

genCoreTestIO :: IO [StubsProgram] -> FilePath -> TestName -> Integer -> TestTree 
genCoreTestIO iprog path tag exp = testCase tag $ do 
    sprog <- iprog 
    i <- corePipeline path sprog
    case i of 
        Just n -> assertEqual "Unexpected value returned" n exp
        Nothing -> assertFailure "Failed to get return value"


corePipelineGlobalTest :: TestTree 
corePipelineGlobalTest = genCoreTestIO (do 
        Some counter <- return $ someSymbol "Counter"
        return [
            SA.StubsProgram{
                SA.stubsEntryPoints=["f","g","j"],
                SA.stubsLibs=[
                    SA.mkStubsLibrary "counter" [
                    SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsUnitRepr
                    },
                    SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.LitExpr $ SA.IntLit 0),SA.Return $  SA.LitExpr $ SA.UnitLit]},
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="inc",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsUnitRepr
                    },
                    SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.GlobalVarLit $ SA.StubsVar "i" SA.StubsIntRepr) ) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr),SA.Return $  SA.LitExpr SA.UnitLit]},

            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="get",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return $ SA.GlobalVarLit $ SA.StubsVar "i" SA.StubsIntRepr]}

                ] [SA.SomeStubsTyDecl (SA.StubsTyDecl counter SA.StubsIntRepr)] [SA.SomeStubsGlobalDecl (SA.StubsGlobalDecl "i" (SA.StubsAliasRepr counter))],
                SA.mkStubsLibrary "core" [
                        SA.SomeStubsFunction SA.StubsFunction {
                            SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="j",
                                SA.sigFnArgTys=Ctx.empty,
                                SA.sigFnRetTy=SA.StubsUnitRepr 
                            },
                            SA.stubFnBody = [SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "init" Ctx.empty SA.StubsUnitRepr ), SA.Return $ SA.LitExpr SA.UnitLit]
                        },
                        SA.SomeStubsFunction SA.StubsFunction {
                            SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="g",
                                SA.sigFnArgTys=Ctx.empty,
                                SA.sigFnRetTy=SA.StubsIntRepr 
                            },
                            SA.stubFnBody = [SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr ), SA.Return $ SA.LitExpr $ SA.IntLit 9] 
                        },
                        SA.SomeStubsFunction SA.StubsFunction {
                            SA.stubFnSig=SA.StubsSignature {
                                SA.sigFnName="f",
                                SA.sigFnArgTys=Ctx.empty,
                                SA.sigFnRetTy=SA.StubsIntRepr 
                            },
                            SA.stubFnBody = [SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr ), SA.Return (SA.AppExpr "get" Ctx.empty SA.StubsIntRepr )] 
                        }
                ] [] []
                ]
            }
            ]
    ) "./tests/test-data/mult.out" "Core Pipeline Global Data" 2

main :: IO ()
main = defaultMain $ do
    testGroup "" [symExecTest, linkerTest,factorialTest,moduleTest, opaqueTest, globalVarTest, opaqueGlobalTest, corePipelinePreambleTest, corePipelineModuleTest,corePipelineOpaqueTest,corePipelineGlobalTest]