-- Tests involving execution of standalone Stubs Programs
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
module StubsStandaloneTests (standaloneTests) where 
import Stubs.AST
import Data.Parameterized
import qualified Data.Parameterized.Nonce as PN
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Stubs.Translate as ST
import qualified Data.Macaw.X86 as DMX
import qualified What4.Interface as WI
import qualified Lang.Crucible.Types as LCT
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Simulator as LCS
import Test.Tasty
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Pipeline as STP
import qualified Lang.Crucible.CFG.SSAConversion as LCSSA
import qualified Data.List as List
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.CFG.Reg as LCCR
import Test.Tasty.HUnit
import qualified Stubs.AST as SA
import qualified Data.BitVector.Sized as BV
import Lang.Crucible.Simulator
import What4.Interface
import What4.Concrete (fromConcreteBV)
import Control.Lens (view)
import qualified Stubs.Arch.X86 ()


-- Test Generators
genTestCaseIO :: IO StubsProgram -> (forall sym ret . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult () sym (DMS.MacawExt DMX.X86_64) (LCS.RegEntry sym ret) -> IO Bool) -> TestName -> TestTree
genTestCaseIO iprog check tag = testCase tag $ do
    Some ng <- PN.newIONonceGenerator
    hAlloc <- LCF.newHandleAllocator
    sprog <- iprog
    cprog <- ST.translateProgram @DMX.X86_64 ng hAlloc [] sprog
    let prog = head cprog
    case lookupEntry (ST.crEntry prog) (ST.crCFGs prog) of
        Nothing -> assertFailure "Translate produced invalid program: no cfg for entry point"
        Just (LCSC.ACFG _ ret icfg) -> do
            res <- STP.smallPipeline prog ( LCSSA.toSSA icfg) f ret (check ret)
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
    cprog <- ST.translateProgram @DMX.X86_64 ng hAlloc [] sprog
    let prog = head cprog
    case lookupEntry (ST.crEntry prog) (ST.crCFGs prog) of
        Nothing -> assertFailure "Translate produced invalid program: no cfg for entry point"
        Just (LCSC.ACFG _ ret icfg) -> do
            res <- STP.smallPipeline prog ( LCSSA.toSSA icfg) f ret (check ret)
            if res then assertBool "" True else assertFailure "Test failed"
    where
        lookupEntry e = List.find (\(LCSC.ACFG _ _ cfg)-> show (LCF.handleName $ LCCR.cfgHandle cfg) == e)
        f :: (forall sym . sym -> Ctx.Assignment LCT.TypeRepr args -> IO (Ctx.Assignment (LCS.RegEntry sym) args))
        f _ assign = case Ctx.viewAssign assign of
            Ctx.AssignEmpty -> return Ctx.empty
            _ -> error "Irrelevant to test"

-- The tests themselves
standaloneTests = [linkerTest,factorialTest,symExecTest,moduleTest,opaqueTest,opaqueGlobalTest,globalVarTest, initHookTest, tupleTest]

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
        SA.stubsModules=[SA.StubsModule{
            SA.fnDecls=[SA.SomeStubsFunction fn, SA.SomeStubsFunction int_fun],
            SA.externSigs=[],
            SA.moduleName="",
            SA.tyDecls=[],
            SA.globalDecls=[]
        }]
    ,SA.stubsInitFns = []}

linkerTest :: TestTree
linkerTest = genTestCase ( SA.StubsProgram {
        SA.stubsModules=[SA.StubsModule{
            SA.fnDecls = [
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "main" Ctx.empty SA.StubsIntRepr) [SA.Return (SA.AppExpr "double" (Ctx.extend Ctx.empty (SA.LitExpr $ SA.IntLit 5)) SA.StubsIntRepr)] ),
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "double" (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) [SA.Return (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) SA.StubsIntRepr)])
        ],
            SA.externSigs=[],
            SA.moduleName="",
            SA.tyDecls=[],
            SA.globalDecls=[]
        }],
        SA.stubsEntryPoints = ["main"]
    ,SA.stubsInitFns = []}) check "Can link preamble into stub"
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
        SA.stubsModules=[SA.StubsModule{
            SA.fnDecls = [
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "main" Ctx.empty SA.StubsIntRepr) [SA.Return (SA.AppExpr "factorial" (Ctx.extend (Ctx.extend Ctx.empty (SA.LitExpr $ SA.IntLit 5)) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr)] ),
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "factorial" (Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) SA.StubsIntRepr)
            [SA.ITE (SA.AppExpr "gt" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.LitExpr $ SA.IntLit 0) ) SA.StubsBoolRepr)
            [SA.Return (SA.AppExpr "factorial"  (Ctx.extend (Ctx.extend Ctx.empty (SA.AppExpr "minus" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) ) (SA.LitExpr $ SA.IntLit 1)) SA.StubsIntRepr ) ) (SA.AppExpr "mult" (Ctx.extend (Ctx.extend Ctx.empty  (SA.ArgLit (SA.StubsArg 1 SA.StubsIntRepr)))  (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) ) SA.StubsIntRepr   )  )  SA.StubsIntRepr)   ]
            [SA.Return (SA.ArgLit (SA.StubsArg 1 SA.StubsIntRepr)) ] ])
        ],
        SA.externSigs = [],
        SA.moduleName="",
        SA.tyDecls=[],
        SA.globalDecls=[]
        }],
        SA.stubsEntryPoints = ["main"]
    ,SA.stubsInitFns = []}) check "calculates factorial of 5"
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
    SA.stubsModules=[
        SA.mkStubsModule "core" [SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="f",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsIntRepr
                    },
                    SA.stubFnBody=[SA.Return $ SA.AppExpr "g" (Ctx.extend Ctx.empty $ SA.LitExpr $ SA.IntLit 20) SA.StubsIntRepr]}] [] [],
        SA.mkStubsModule "internal" [SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="g",
                    SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
                    SA.sigFnRetTy=SA.StubsIntRepr
                },
            SA.stubFnBody=[SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr)  (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)), SA.Return (SA.VarLit (SA.StubsVar "v" SA.StubsIntRepr))]
            }] [] []
     ]
,SA.stubsInitFns = []} check "Module Test"
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
        SA.stubsModules=[
            SA.mkStubsModule "counter" [
            SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsAliasRepr counter
                    },
                    SA.stubFnBody=[SA.Return $  SA.LitExpr $ SA.IntLit 0]},
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
        ] [SA.SomeStubsTyDecl (SA.StubsTyDecl counter SA.StubsIntRepr)] [],
            SA.mkStubsModule "core" [
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
        ]   ,SA.stubsInitFns = []}) check "Opaque Test"
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
        SA.stubsModules = [
            SA.mkStubsModule "internal" [
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
            SA.mkStubsModule "core" [
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
    ,SA.stubsInitFns = []} check "Basic Global Variable functionality"
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
            SA.stubsModules=[
                SA.mkStubsModule "counter" [
                    SA.SomeStubsFunction
                SA.StubsFunction {
                    SA.stubFnSig=SA.StubsSignature{
                    SA.sigFnName="init",
                    SA.sigFnArgTys=Ctx.empty,
                    SA.sigFnRetTy=SA.StubsUnitRepr
                    },
                    SA.stubFnBody=[SA.GlobalAssignment (SA.StubsVar "i" SA.StubsIntRepr) (SA.LitExpr $ SA.IntLit 0),SA.Return $  SA.LitExpr SA.UnitLit]},
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
                SA.mkStubsModule "core"  [
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
            ,SA.stubsInitFns = []}
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


initHookTest :: TestTree
initHookTest = genTestCaseIO (do
        Some counter <- return $ someSymbol "Counter"
        return SA.StubsProgram {
            SA.stubsEntryPoints=["main"],
            SA.stubsModules=[
                SA.mkStubsModule "counter" [
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
                SA.mkStubsModule "core"  [
                    SA.SomeStubsFunction (
                    SA.StubsFunction{
                        SA.stubFnSig=SA.StubsSignature{
                            SA.sigFnName="main",
                            SA.sigFnArgTys=Ctx.empty,
                            SA.sigFnRetTy=SA.StubsIntRepr
                        },
                        SA.stubFnBody=[SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr), SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr),SA.Assignment (SA.StubsVar "_" SA.StubsUnitRepr) (SA.AppExpr "inc" Ctx.empty SA.StubsUnitRepr), SA.Return (SA.AppExpr "get" Ctx.empty SA.StubsIntRepr)]
                    }
                )
                ]
                [] []
            ]
            ,SA.stubsInitFns = ["init"]}
            ) check "Init hook runs properly"
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

tupleTest :: TestTree 
tupleTest = let pointTy = Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr  in genTestCase SA.StubsProgram {
        SA.stubsModules = [
            SA.mkStubsModule "point"  [
                SA.SomeStubsFunction 
                    SA.StubsFunction {
                        SA.stubFnSig=SA.StubsSignature "mkPoint" pointTy (SA.StubsTupleRepr pointTy) ,
                        SA.stubFnBody=[SA.Return (SA.TupleExpr (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.ArgLit (SA.StubsArg 1 SA.StubsIntRepr)) ))]
                    },
                SA.SomeStubsFunction 
                    SA.StubsFunction {
                        SA.stubFnSig=SA.StubsSignature "dist" (Ctx.extend Ctx.empty (SA.StubsTupleRepr pointTy)) SA.StubsIntRepr,
                        SA.stubFnBody=[
                            SA.Return (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.TupleAccessExpr (SA.ArgLit $ SA.StubsArg 0 (SA.StubsTupleRepr pointTy)) 0 SA.StubsIntRepr)) 
                            (SA.TupleAccessExpr (SA.ArgLit $ SA.StubsArg 0 (SA.StubsTupleRepr pointTy)) 1 SA.StubsIntRepr)) SA.StubsIntRepr )
                        ]
                    }
            ] [] [],
        SA.mkStubsModule "core" [
            SA.SomeStubsFunction SA.StubsFunction {
                SA.stubFnSig= SA.StubsSignature "main" Ctx.empty SA.StubsIntRepr,
                SA.stubFnBody=[
                    SA.Assignment (SA.StubsVar "p" $ SA.StubsTupleRepr pointTy) (SA.AppExpr "mkPoint" (Ctx.extend (Ctx.extend Ctx.empty (SA.LitExpr $ SA.IntLit 3)) (SA.LitExpr $ SA.IntLit 5))  $ SA.StubsTupleRepr pointTy ),
                    SA.Return (SA.AppExpr "dist" (Ctx.extend Ctx.empty (SA.VarLit (SA.StubsVar "p" $ SA.StubsTupleRepr pointTy))) SA.StubsIntRepr)]
            } 
        ] [] []
     ],
     SA.stubsEntryPoints=["main"],
     SA.stubsInitFns=[]
    } check "Tuple functionality"
    where
        check :: (forall sym . WI.IsExprBuilder sym => LCT.TypeRepr ret -> LCSE.ExecResult p sym ext (LCS.RegEntry sym ret) -> IO Bool)
        check retRepr crucibleRes = case crucibleRes of
                FinishedResult _ r -> case r of
                                        TotalRes v -> do
                                            let q = view gpValue v
                                            case retRepr of
                                                LCT.BVRepr _ -> case asConcrete $ regValue q of
                                                    Just k -> if BV.asUnsigned (fromConcreteBV k) == 8 then return True else print ("Unexpected value received: " ++ show (BV.asUnsigned (fromConcreteBV k))) >> return False
                                                    Nothing -> print "Failed to concretize return" >> return False
                                                _ -> print "Unexpected return type" >> return False
                                        _ -> print "Failed to get complete result" >> return False
                AbortedResult _ (AbortedExec r _) -> print ("Aborted Execution:" ++ show r) >> return False
                _ -> print "Failed to finish execution" >> return False
