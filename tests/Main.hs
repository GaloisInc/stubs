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

import qualified Stubs.Loader as SL
import qualified Stubs.Solver as S
import Stubs.EntryPoint as SE
import qualified Stubs.Memory as SM
import qualified Data.ByteString as B
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Data.Parameterized.Nonce as PN
import Data.Parameterized.Some
import qualified Lang.Crucible.Backend as LCB
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.Symbolic as DMS
import qualified Stubs.FunctionOverride.Extension as SFE
import qualified Stubs.SymbolicExecution as SVS
import qualified Stubs.EnvVar as SEnv
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lumberjack as LJ
import qualified Stubs.EntryPoint as SEp
import qualified Stubs.Diagnostic as SD
import qualified Data.BitVector.Sized as BV
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.RegMap (RegEntry(regValue))
import Control.Lens
import Data.Macaw.Symbolic (GenArchVals (lookupReg), SymArchConstraints)
import What4.Interface (asConcrete, IsExpr (asInteger))
import What4.Concrete (fromConcreteBV)
import Stubs.Wrapper
import Infrastructure as SI
import qualified Stubs.Parser as SP
import qualified Data.Parameterized.Context.Unsafe as Ctx
import qualified Lang.Crucible.CFG.Expr as LCCE
import Data.Parameterized.Nonce (NonceGenerator)
import Lang.Crucible.FunctionHandle (HandleAllocator)
import Data.Macaw.CFG as DMC
import Stubs.FunctionOverride.Extension.Types as SFT
import Stubs.AST as SA
import qualified Stubs.Translate as ST

import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified Data.Macaw.X86 as DMX
import qualified Data.List as List
import qualified Lang.Crucible.CFG.Core as LCSC
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.CFG.SSAConversion as LCSSA
import qualified Lang.Crucible.Simulator.RegMap as LCSR
import qualified What4.Interface as WI
import qualified Lang.Crucible.Simulator as LCSE
import qualified Stubs.Preamble as SPR
import Stubs.Preamble.X86 () --for instance

logShim:: SD.Diagnostic -> IO ()
logShim _ = putStrLn ""
--Should refactor so as to remove flag later
pipelineTest :: FilePath -> Bool -> IO (Maybe Integer)
pipelineTest path parserFlag = do
    contents <- B.readFile path
    hAlloc <- LCF.newHandleAllocator
    let pinst = ProgramInstance{ piPath=path,
                                 piBinary=contents,
                                 piFsRoot=Nothing,
                                 piCommandLineArguments=[],
                                 piConcreteEnvVars=[],
                                 piConcreteEnvVarsFromBytes=[],
                                 piSymbolicEnvVars=[],
                                 piSolver=S.Z3,
                                 piFloatMode=S.IEEE,
                                 piEntryPoint=SE.DefaultEntryPoint,
                                 piMemoryModel=SM.DefaultMemoryModel,
                                 piOverrideDir=Just "./tests/test-data/libc-overrides",
                                 piIterationBound=Nothing,
                                 piRecursionBound=Nothing,
                                 piSolverInteractionFile=Nothing,
                                 piSharedObjectDir=Nothing,
                                 piLogSymbolicBranches=Nothing,
                                 piLogFunctionCalls=Nothing
                                 }
    let logAction= LJ.LogAction logShim
    Some ng <- PN.newIONonceGenerator
    S.withOnlineSolver (piSolver pinst) (piFloatMode pinst) ng $ \bak -> do
        let sym = LCB.backendGetSym bak
        (recordFn, _) <- buildRecordLLVMAnnotation
        let ?recordLLVMAnnotation = recordFn
        SL.withBinary path contents Nothing hAlloc sym $ \archInfo _ archVals buildSyscallABI buildFunctionABI parserHooks buildGlobals _ binConf funAbiExt -> DMA.withArchConstraints archInfo $  do
            Just (SL.FunABIExt reg) <- return funAbiExt
            -- why is this necessary?
            let ?memOpts = LCLM.defaultMemOptions
            -- load the overrides
            csOverrides <-
                (if parserFlag then loadStubsCFG ng hAlloc else loadParsedOverride (piOverrideDir pinst) ng hAlloc parserHooks)
            -- setup environment to execute
            let execFeatures = []
            let seConf = SVS.SymbolicExecutionConfig
                     { SVS.secSolver = piSolver pinst
                     , SVS.secLogBranches = False
                     }
            let fnConf = SVS.FunctionConfig {
                SVS.fcBuildSyscallABI = buildSyscallABI
                , SVS.fcBuildFunctionABI = buildFunctionABI
                , SVS.fcCrucibleSyntaxOverrides = csOverrides
            }
            envVarMap <- SEnv.mkEnvVarMap bak (piConcreteEnvVars pinst) (piConcreteEnvVarsFromBytes pinst) (piSymbolicEnvVars pinst)

            -- execute symbolically
            entryPointAddr <- SEp.resolveEntryPointAddrOff binConf $ piEntryPoint pinst
            ambientExecResult <- SVS.symbolicallyExecute logAction bak hAlloc archInfo archVals seConf execFeatures entryPointAddr (piMemoryModel pinst) buildGlobals (piFsRoot pinst) (piLogFunctionCalls pinst) binConf fnConf (piCommandLineArguments pinst) envVarMap
            let crucibleRes = SVS.serCrucibleExecResult ambientExecResult
            case crucibleRes of
                FinishedResult _ r -> case r of
                                        TotalRes v -> do
                                            let q = view gpValue v
                                            let g = lookupReg archVals q reg
                                            let LCLM.LLVMPointer _ bv = regValue g
                                            let t = asConcrete bv
                                            case t of
                                                Nothing -> return Nothing
                                                Just cv -> return $ Just (BV.asUnsigned $ fromConcreteBV cv)
                                        _ -> return Nothing
                _ -> return Nothing

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

loadStubsCFG :: forall ext s w p sym arch. (LCCE.IsSyntaxExtension ext, ext ~ DMS.MacawExt arch, w ~ ArchAddrWidth arch, MemWidth w,SymArchConstraints arch, SPR.Preamble arch) => NonceGenerator IO s -> HandleAllocator -> IO (SFT.CrucibleSyntaxOverrides w p sym arch)
loadStubsCFG _ _ = do -- need args to match scope parameter
    loadStubsPrograms [testProg]

loadParsedOverride dir ng hAlloc parserHooks = do
    case dir of
        Just dir -> do
            -- SFE.loadCrucibleSyntaxOverrides abi dir (piCCompiler pinst) ng hAlloc parserHooks --original pipeline
            (overrides, startupOverrides, funAddrOverrides) <- SP.parseCrucibleOverrides dir ng hAlloc parserHooks
            loadParsedPrograms overrides startupOverrides funAddrOverrides
        Nothing -> return SFE.emptyCrucibleSyntaxOverrides

testProg :: StubsProgram
testProg =
    let fn = SA.StubsFunction {
        SA.stubFnSig=SA.StubsSignature{
            SA.sigFnName="f",
            SA.sigFnArgTys=Ctx.empty,
            SA.sigFnRetTy=SA.StubsIntRepr
        },
        SA.stubFnBody=[SA.Return $ SA.AppExpr "g" (Ctx.extend Ctx.empty $ SA.IntLit 20) SA.StubsIntRepr]
    } in let int_fun = SA.StubsFunction {
        SA.stubFnSig=SA.StubsSignature{
            SA.sigFnName="g",
            SA.sigFnArgTys=Ctx.extend Ctx.empty SA.StubsIntRepr,
            SA.sigFnRetTy=SA.StubsIntRepr
        },
        SA.stubFnBody=[SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr)  (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)), SA.Return (SA.VarLit (SA.StubsVar "v" SA.StubsIntRepr))]
    } in SA.StubsProgram {
        SA.stubsMain="f",
        SA.stubsFnDecls = [SA.SomeStubsFunction fn, SA.SomeStubsFunction int_fun]
    }

symExecTest :: TestTree
symExecTest = testCase "" $ do
    Some ng <- PN.newIONonceGenerator
    hAlloc <- LCF.newHandleAllocator
    prog <- ST.translateProgram @DMX.X86_64 ng hAlloc testProg
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

overrideTest :: TestTree
overrideTest = testCase "" $ do
    res <- pipelineTest "./tests/test-data/a.out" False
    case res of
        Nothing -> assertFailure "Failed to get value"
        Just x -> assertEqual "Values not equal: Parser-Based Test" x 20

overrideWrapperTest :: TestTree
overrideWrapperTest = testCase "" $ do
    res <- pipelineTest "./tests/test-data/a.out" True
    case res of
        Nothing -> assertFailure "Failed to get value"
        Just x -> assertEqual "Values not equal: Parser-less Test" x 20


linkerTest :: TestTree 
linkerTest = testCase "Can link preamble into stub properly" $ do 
    let sprog = SA.StubsProgram {
        SA.stubsFnDecls = [
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "main" Ctx.empty SA.StubsIntRepr) [SA.Return (SA.AppExpr "double" (Ctx.extend Ctx.empty (SA.IntLit 5)) SA.StubsIntRepr)] ),
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "double" (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) [SA.Return (SA.AppExpr "plus" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) SA.StubsIntRepr)])
        ],
        SA.stubsMain = "main",
        SA.stubsTyDecls = []::[SA.StubsTyDecl]
    }
    Some ng <- PN.newIONonceGenerator
    hAlloc <- LCF.newHandleAllocator
    prog <- ST.translateProgram @DMX.X86_64 ng hAlloc sprog
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
factorialTest = testCase "calculates factorial" $ do 
    let sprog = SA.StubsProgram {
        SA.stubsFnDecls = [
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "main" Ctx.empty SA.StubsIntRepr) [SA.Return (SA.AppExpr "factorial" (Ctx.extend (Ctx.extend Ctx.empty (SA.IntLit 5)) (SA.IntLit 1)) SA.StubsIntRepr)] ),
            SA.SomeStubsFunction (SA.StubsFunction (SA.StubsSignature "factorial" (Ctx.extend (Ctx.extend Ctx.empty SA.StubsIntRepr) SA.StubsIntRepr) SA.StubsIntRepr) 
            [SA.ITE (SA.AppExpr "gt" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr))) (SA.IntLit 0) ) SA.StubsBoolRepr) 
            [SA.Return (SA.AppExpr "factorial"  (Ctx.extend (Ctx.extend Ctx.empty (SA.AppExpr "minus" (Ctx.extend (Ctx.extend Ctx.empty (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) ) (SA.IntLit 1)) SA.StubsIntRepr ) ) (SA.AppExpr "mult" (Ctx.extend (Ctx.extend Ctx.empty  (SA.ArgLit (SA.StubsArg 1 SA.StubsIntRepr)))  (SA.ArgLit (SA.StubsArg 0 SA.StubsIntRepr)) ) SA.StubsIntRepr   )  )  SA.StubsIntRepr)   ] 
            [(SA.Return (SA.ArgLit (SA.StubsArg 1 SA.StubsIntRepr)) )] ])
        ],
        SA.stubsMain = "main",
        SA.stubsTyDecls = []::[SA.StubsTyDecl]
    }
    Some ng <- PN.newIONonceGenerator
    hAlloc <- LCF.newHandleAllocator
    prog <- ST.translateProgram @DMX.X86_64 ng hAlloc sprog
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

main :: IO ()
main = defaultMain $ do
    testGroup "" [overrideTest,overrideWrapperTest,symExecTest, linkerTest,factorialTest]