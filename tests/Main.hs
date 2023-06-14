{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

module Main ( main ) where

import qualified System.IO as IO
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
import Data.Maybe
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.RegMap (RegEntry(regValue))
import Control.Lens
import Control.Monad.IO.Class
import Data.Macaw.Symbolic (GenArchVals (lookupReg), SymArchConstraints)
import What4.Interface (asConcrete, IsExpr (asInteger))
import What4.Concrete (fromConcreteBV)
import Stubs.Wrapper
import Infrastructure as SI
import Stubs.Parser as SP
import What4.FunctionName as WF
import Data.Parameterized.Context.Unsafe as Ctx
import qualified Lang.Crucible.Types as LCT
import Lang.Crucible.CFG.Reg as LCCR
import Lang.Crucible.CFG.Expr as LCCE
import Lang.Crucible.CFG.Generator as LCCG
import What4.ProgramLoc (Position(InternalPos))
import Lang.Crucible.Syntax.Concrete (ACFG(ACFG), ParsedProgram (parsedProgCFGs))
import Data.Parameterized.Nonce (NonceGenerator)
import Lang.Crucible.FunctionHandle (HandleAllocator)
import qualified Data.Parameterized.NatRepr as PN
import Data.Macaw.CFG as DMC
import Data.Map as Map
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import Stubs.FunctionOverride.Extension.Types as SFT
import Stubs.AST as SA
import Stubs.Translate as ST

libcdir = "./tests/test-data/libc-overrides"
logShim:: SD.Diagnostic -> IO ()
logShim _ = putStrLn ""
--Should refactor so as to remove flag later
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
                                 piOverrideDir=Just libcdir,
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
        SL.withBinary path contents Nothing hAlloc sym $ \archInfo abi archVals buildSyscallABI buildFunctionABI parserHooks buildGlobals numBytes binConf funAbiExt -> DMA.withArchConstraints archInfo $  do
            Just (SL.FunABIExt reg) <- return funAbiExt
            -- why is this necessary?
            let ?memOpts = LCLM.defaultMemOptions
            -- load the overrides
            csOverrides <-
                (if parserFlag then loadManualCFG ng hAlloc else loadParsedOverride (piOverrideDir pinst) ng hAlloc parserHooks)
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

loadManualCFG :: forall ext s w p sym arch. (IsSyntaxExtension ext, ext ~ DMS.MacawExt arch, w ~ ArchAddrWidth arch, MemWidth w,SymArchConstraints arch) => NonceGenerator IO s -> HandleAllocator -> IO (SFT.CrucibleSyntaxOverrides w p sym arch)
loadManualCFG ng hAlloc = do
    f <- stubsCfgTest ng hAlloc
    print (parsedProgCFGs f)
    let overrides = [(libcdir++"/function/f.cbl",f)]
    loadParsedPrograms overrides [] []

loadParsedOverride dir ng hAlloc parserHooks = do
    case dir of
        Just dir -> do
            -- SFE.loadCrucibleSyntaxOverrides abi dir (piCCompiler pinst) ng hAlloc parserHooks --original pipeline
            (overrides, startupOverrides, funAddrOverrides) <- SP.parseCrucibleOverrides dir ng hAlloc parserHooks
            loadParsedPrograms overrides startupOverrides funAddrOverrides
        Nothing -> return SFE.emptyCrucibleSyntaxOverrides

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

main :: IO ()
main = defaultMain $ do
    testGroup "" [overrideTest,overrideWrapperTest]

manualCfgTest :: forall ext s w arch. (IsSyntaxExtension ext, ext ~ DMS.MacawExt arch, w ~ ArchAddrWidth arch, MemWidth w) => NonceGenerator IO s -> HandleAllocator -> IO (LCSC.ParsedProgram ext)
manualCfgTest ng hAlloc = do
    let n = memWidthNatRepr @w
    Some one <- return $ PN.mkNatRepr 1
    Just PN.LeqProof <- return $ PN.testLeq one n
    let intTy = LCT.BVRepr n
    let v = LCCR.App  $ LCCE.IntLit 20
    let args = Ctx.extend Ctx.empty intTy
    let ret = intTy
    testHandle <- LCF.mkHandle' hAlloc (WF.functionNameFromText "f") args ret
    (SomeCFG q,_) <- LCCG.defineFunction @_ @ext InternalPos (Some ng) testHandle $ const (Const (), returnFromFunction $ LCCR.App (LCCE.IntegerToBV n v))
    let prog = LCSC.ParsedProgram {
        LCSC.parsedProgGlobals = Map.empty,
        LCSC.parsedProgExterns = Map.empty,
        LCSC.parsedProgCFGs = [ACFG args ret q],
        LCSC.parsedProgForwardDecs = Map.empty
    }
    return prog

stubsCfgTest :: forall ext s w arch. (IsSyntaxExtension ext, ext ~ DMS.MacawExt arch, SymArchConstraints arch) => NonceGenerator IO s -> HandleAllocator -> IO (LCSC.ParsedProgram ext)
stubsCfgTest ng halloc = do
    let fn = StubsFunction {
        stubFnName="f",
        stubFnArgTys=Ctx.extend Ctx.empty StubsIntRepr,
        stubFnRetTy=StubsIntRepr,
        stubFnBody=[SA.Assignment (SA.StubsVar "v" SA.StubsIntRepr)  (SA.IntLit 20), SA.Return (SA.VarLit (SA.StubsVar "v" SA.StubsIntRepr))]
    }
    ST.translateDecls ng halloc [SomeStubsFunction fn]