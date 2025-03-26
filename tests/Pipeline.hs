{-#LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# HLINT ignore "Use if" #-}
{-# LANGUAGE TypeOperators #-}

module Pipeline where
import qualified Stubs.AST as SA
import qualified Data.ByteString as B
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Data.Parameterized.Nonce as PN
import qualified Stubs.SymbolicExecution as SVS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Stubs.Loader as SL
import qualified Lang.Crucible.Backend as LCB
import qualified Stubs.Solver as AS
import Data.Parameterized (Some(..))
import qualified Stubs.Translate as ST
import qualified Stubs.EnvVar as AEnv
import qualified Stubs.EntryPoint as AEp
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Data.BitVector.Sized as BV
import qualified Data.Macaw.Symbolic as DMS
import qualified Stubs.Preamble as SPR
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified What4.Interface as WI
import qualified Lang.Crucible.Simulator as LCS
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.Types as LCT
import qualified Stubs.Memory as SM
import Infrastructure
import What4.Concrete (fromConcreteBV)
import Lang.Crucible.Simulator
import Data.Macaw.Symbolic (lookupReg)
import What4.Interface (asConcrete)
import Control.Lens (view)
import qualified Stubs.Translate.Core as STC
import Stubs.Memory
import qualified Stubs.Common as SC
import qualified Stubs.Logging as SLg
import qualified Lang.Crucible.Simulator.CallFrame as LCSCF
import qualified Stubs.Parser as SP
import Control.Monad.Except


parserCorePipeline :: FilePath -> [FilePath] -> [String]  -> IO (Maybe Integer)
parserCorePipeline path progs entries = do
    i <- runExceptT (SP.parseStubsOverrides progs entries)
    case i of
        Left err -> fail (show err)
        Right stubProg -> do
            corePipeline path [stubProg]

corePipeline :: FilePath -> [SA.StubsProgram] -> IO (Maybe Integer)
corePipeline path stubProgs = do
    contents <- B.readFile path
    hAlloc <- LCF.newHandleAllocator
    let pinst = ProgramInstance{ piPath=path,
                                 piBinary=contents,
                                 piFsRoot=Nothing,
                                 piCommandLineArguments=[],
                                 piConcreteEnvVars=[],
                                 piConcreteEnvVarsFromBytes=[],
                                 piSymbolicEnvVars=[],
                                 piSolver=AS.Z3,
                                 piFloatMode=AS.IEEE,
                                 piEntryPoint=AEp.DefaultEntryPoint,
                                 piMemoryModel=SM.DefaultMemoryModel,
                                 piOverrideDir=Nothing,
                                 piIterationBound=Nothing,
                                 piRecursionBound=Nothing,
                                 piSolverInteractionFile=Nothing,
                                 piSharedObjectDir=Nothing,
                                 piLogSymbolicBranches=Nothing,
                                 piLogFunctionCalls=Nothing
                                 }
    let logAction= SLg.emptyLogger
    Some ng <- PN.newIONonceGenerator
    AS.withOnlineSolver (piSolver pinst) (piFloatMode pinst) ng $ \bak-> do
        let tsym = SC.Sym (LCB.backendGetSym bak) bak
        (recordFn, _) <- buildRecordLLVMAnnotation
        let ?recordLLVMAnnotation = recordFn
        SL.withBinary path contents Nothing hAlloc tsym $ \archInfo _ archVals buildSyscallABI buildFunctionABI _ _ binConf funAbiExt ovs-> DMA.withArchConstraints archInfo $  do
            Just (SL.FunABIExt reg) <- return funAbiExt
            let ?memOpts = LCLM.defaultMemOptions
            let abiConf = SVS.ABIConfig {
                SVS.abiBuildFunctionABI = buildFunctionABI,
                SVS.abiBuildSyscallABI=buildSyscallABI
            }
            crucProgs <- fmap concat (mapM (ST.translateProgram ng hAlloc ovs) stubProgs)
            envVarMap <- AEnv.mkEnvVarMap bak (piConcreteEnvVars pinst) (piConcreteEnvVarsFromBytes pinst) (piSymbolicEnvVars pinst)

            -- execute symbolically
            entryPointAddr <- AEp.resolveEntryPointAddrOff binConf $ piEntryPoint pinst
            ambientExecResult <- SVS.symbolicallyExecute logAction bak hAlloc archInfo archVals (SVS.SymbolicExecutionConfig{SVS.secLogBranches=False,SVS.secSolver=piSolver pinst}) [] entryPointAddr binConf abiConf (piCommandLineArguments pinst) envVarMap crucProgs
            let crucibleRes = SVS.serCrucibleExecResult ambientExecResult
            case crucibleRes of
                                LCSE.FinishedResult _ r -> case r of
                                        LCSE.TotalRes v -> do
                                            let q = view gpValue v
                                            let g = lookupReg archVals q reg
                                            let LCLM.LLVMPointer _ bv = regValue g
                                            let t = asConcrete bv
                                            case t of
                                                Nothing -> return Nothing
                                                Just cv -> return $ Just (BV.asUnsigned $ fromConcreteBV cv)
                                        _ -> return Nothing
                                -- Failed, so try to dump some useful information
                                LCSE.AbortedResult _ r -> do
                                    putStrLn "Execution aborted"
                                    case r of
                                        LCSE.AbortedExec re st -> do
                                            print re
                                            let tau = view gpValue st
                                            case tau of
                                                LCSCF.OF _ -> print "in override"
                                                LCSCF.MF _ -> print "in crucible code"
                                                _ -> print "while returning"
                                            return Nothing
                                        _ -> putStrLn "Cause unexpected: either exit() or multiple branches failed" >> return Nothing
                                _ -> return Nothing

smallPipeline :: forall arch args ret ext p. (DMS.SymArchConstraints arch, ext ~ DMS.MacawExt arch, p ~ (), SPR.Preamble arch, STC.StubsArch arch) =>
                                        ST.CrucibleProgram arch ->
                                        LCCC.SomeCFG (DMS.MacawExt arch) args ret ->
                                        (forall sym . sym -> Ctx.Assignment LCT.TypeRepr args -> IO (Ctx.Assignment (LCS.RegEntry sym) args)) ->
                                        LCT.TypeRepr ret->
                                        (forall sym . WI.IsExprBuilder sym => LCSE.ExecResult p sym ext (LCS.RegEntry sym ret) -> IO Bool) ->
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
                                 piSolver=AS.Z3,
                                 piFloatMode=AS.IEEE,
                                 piEntryPoint=AEp.DefaultEntryPoint,
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
    AS.withOnlineSolver (piSolver pinst) (piFloatMode pinst) ng $ \bak -> do
        let sym = LCB.backendGetSym bak

        LCCC.SomeCFG unwrappedCfg <- return cfg
        args <- argsf sym (LCCC.cfgArgTypes unwrappedCfg)

        symexec bak hAlloc prog cfg args ret check []
