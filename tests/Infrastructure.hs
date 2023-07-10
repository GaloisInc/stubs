-- Module containing miscaellaneous testing infrastructure inherited from Ambient
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ImplicitParams #-}
module Infrastructure
    (
        buildRecordLLVMAnnotation,
        ProgramInstance(..),
        symexec,
        SomeRegEntry(..),
        corePipeline,
        logShim
    )
where

import           Control.Monad.IO.Class (liftIO, MonadIO )
import qualified Data.ByteString as BS
import           Data.IORef ( IORef, newIORef, modifyIORef')
import qualified Data.Map as Map


import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.Errors as LCLE
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.CallStack as LCLMC
import qualified Lang.Crucible.LLVM.MemModel.Partial as LCLMP

import           Data.Word ( Word64 )

import qualified Stubs.EntryPoint as AEp
import qualified Stubs.EnvVar as AEnv

import qualified Stubs.Memory as AM
import qualified Stubs.Solver as AS
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Data.Macaw.Symbolic as DMS

import           Data.Macaw.BinaryLoader.X86 ()

import           Data.Macaw.X86.Symbolic ()
import qualified Lang.Crucible.FunctionHandle as LCF

import qualified What4.Interface as WI
import qualified Lang.Crucible.CFG.Expr as LCCE
import Lang.Crucible.Simulator (RegEntry (regValue), gpValue)
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.LLVM.Intrinsics as LCLI
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified System.IO as IO
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.CFG.SSAConversion as LCSSA
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr.Builder as WE
import qualified What4.Protocol.Online as WPO
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Control.Monad.Catch as CMC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Macaw.CFG as DMC
import qualified Stubs.Translate as ST
import qualified Stubs.Translate.Core as STC
import qualified Lumberjack as LJ
import qualified Data.Parameterized.Nonce as PN
import Data.Parameterized (Some(..))
import qualified Stubs.EntryPoint as SE
import qualified Stubs.Loader as SL
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Stubs.SymbolicExecution as SVS
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as B
import qualified Stubs.AST as SA
import What4.Interface (asConcrete)
import What4.Concrete (fromConcreteBV)
import Data.Macaw.Symbolic (lookupReg)
import Control.Lens (view)
import qualified Stubs.Diagnostic as SD

-- | Build an LLVM annotation tracker to record instances of bad behavior
-- checks.  Bad behavior encompasses both undefined behavior, and memory
-- errors.  This function returns a function to set '?recordLLVMAnnotation' to,
-- as well as a reference to the record of bad behaviors that will be built up.
buildRecordLLVMAnnotation
  :: LCB.IsSymInterface sym
  => IO ( LCLMC.CallStack -> LCLMP.BoolAnn sym -> LCLE.BadBehavior sym -> IO ()
        , IORef (LCLM.LLVMAnnMap sym) )
buildRecordLLVMAnnotation = do
  badBehavior <- liftIO $ newIORef Map.empty
  let recordFn = \cs ann behavior ->
        modifyIORef' badBehavior (Map.insert ann (cs, behavior))
  return (recordFn , badBehavior)

-- | A definition of the initial state of a program to be verified
--
-- Currently, this just defines the /concrete/ initial state of the
-- program. This will be extended later to support explicitly symbolic initial
-- states.
data ProgramInstance =
  ProgramInstance { piPath :: FilePath
                  -- ^ The path to the binary on disk (or a synthetic name)
                  , piBinary :: BS.ByteString
                  -- ^ The contents of the binary to verify, which will be
                  -- parsed and lifted into the verification IR
                  , piFsRoot :: Maybe FilePath
                  -- ^ Path to the symbolic file system.  If this is 'Nothing',
                  -- the file system will be empty.
                  , piCommandLineArguments :: [BS.ByteString]
                  -- ^ The command line arguments to pass to the program
                  --
                  -- The caller should ensure that this includes argv[0] (the
                  -- program name)
                  --
                  -- Note that the command line UI can take textual arguments;
                  -- the real arguments here are 'BS.ByteString's because that
                  -- is how they must be represented in the memory model.
                  , piConcreteEnvVars :: [AEnv.ConcreteEnvVar BS.ByteString]
                  -- ^ The environment variables to pass to the program, where
                  -- the values are concrete.
                  , piConcreteEnvVarsFromBytes :: [AEnv.ConcreteEnvVarFromBytes BS.ByteString]
                  -- ^ The environment variables to pass to the program, where
                  -- the values are concrete bytes contained in a file.
                  , piSymbolicEnvVars :: [AEnv.SymbolicEnvVar BS.ByteString]
                  -- ^ The environment variables to pass to the program, where
                  -- the values are symbolic.
                  , piSolver :: AS.Solver
                  -- ^ The solver to use for path satisfiability checking and
                  -- goals
                  , piFloatMode :: AS.FloatMode
                  -- ^ The interpretation of floating point operations in SMT
                  , piEntryPoint :: AEp.EntryPoint
                  -- ^ Where to begin simulation
                  , piMemoryModel :: AM.MemoryModel ()
                  -- ^ Which memory model configuration to use
                  , piOverrideDir :: Maybe FilePath
                  -- ^ Path to the crucible syntax overrides directory.  If
                  -- this is 'Nothing', then no crucible syntax overrides will
                  -- be registered.
                  , piIterationBound :: Maybe Word64
                  -- ^ If @'Just' n@, bound all loops to at most @n@ iterations.
                  -- If 'Nothing', do not bound the number of loop iterations.
                  , piRecursionBound :: Maybe Word64
                  -- ^ If @'Just' n@, bound the number of recursive calls to at
                  -- most @n@ calls. If 'Nothing', do not bound the number of
                  -- recursive calls.
                  , piSolverInteractionFile :: Maybe FilePath
                  -- ^ Optional location to write solver interactions log to
                  , piSharedObjectDir :: Maybe FilePath
                  -- ^ Optional directory containing shared objects to verify
                  , piLogSymbolicBranches :: Maybe FilePath
                  -- ^ Log symbolic branches to a given file
                  , piLogFunctionCalls :: Maybe FilePath
                  -- ^ Optional location to log function calls to
                  }

data SomeRegEntry tp = forall sym . (WI.IsExprBuilder sym) => SomeRegEntry (RegEntry sym tp)

logShim:: SD.Diagnostic -> IO ()
logShim _ = return ()

symexec
  :: forall m ext arch sym bak scope st fs solver p w args ret a. ( CMC.MonadThrow m
     , MonadIO m
     , ext ~ DMS.MacawExt arch
     , LCCE.IsSyntaxExtension ext
     , LCB.IsSymBackend sym bak
     , DMS.SymArchConstraints arch
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , p ~ ()
     , (w ~ DMC.ArchAddrWidth arch )
     )
  => bak
  -> LCF.HandleAllocator
  -- ^ Configuration parameters concerning functions and overrides
  -> ST.CrucibleProgram arch
  -> LCCC.SomeCFG ext args ret
  -> Ctx.Assignment (LCS.RegEntry sym) args
  -> LCT.TypeRepr ret
  -> (WI.IsExprBuilder sym => (LCSE.ExecResult p sym ext (LCS.RegEntry sym ret)) -> m a)
  -> m a
symexec bak halloc prog cfg args retRepr check = do
  LCCC.SomeCFG cfg <- return cfg

  let simAction = LCS.runOverrideSim retRepr $ do
                    -- First, initialize the symbolic file system...
                    --initFSOverride
                    -- ...then simulate any startup overrides...
                    -- ...and finally, run the entrypoint function.
                    LCS.regValue <$> LCS.callCFG cfg (LCS.RegMap args)

  let cfgs = ST.crCFGs prog
  let hdlMap = foldr (\(LCSC.ACFG _ _ icfg) acc -> case LCSSA.toSSA icfg of
            (LCCC.SomeCFG ccfg) -> LCF.insertHandleMap (LCCC.cfgHandle ccfg)
                                       (LCS.UseCFG ccfg (LCAP.postdomInfo ccfg))
                                       acc
        ) LCF.emptyHandleMap cfgs

  let bindings = LCF.insertHandleMap (LCCC.cfgHandle cfg)
                                       (LCS.UseCFG cfg (LCAP.postdomInfo cfg))
                                       hdlMap

  -- Link preamble
  let wrappedovs = ST.crFnHandleMap prog
  let linkedMap = foldr (\(ST.SomeWrappedOverride (ST.WrappedOverride ovf (STC.StubHandle _ _ h))) acc -> LCF.insertHandleMap h (LCS.UseOverride (ovf bak)) acc) bindings wrappedovs

  let emptyExt = LCSE.ExtensionImpl
          { LCSE.extensionEval = \_sym _iTypes _log _f _state -> \case
          , LCSE.extensionExec = \case
          }
  let ctx = LCS.initSimContext bak (MapF.union LCLI.llvmIntrinsicTypes LCLS.llvmSymIOIntrinsicTypes) halloc IO.stdout (LCS.FnBindings linkedMap) emptyExt ()
  let s0 = LCS.InitialState ctx LCSG.emptyGlobals LCS.defaultAbortHandler retRepr simAction

  res <- liftIO $ LCS.executeCrucible [] s0
  check res

corePipeline :: FilePath -> [SA.StubsProgram] ->  IO (Maybe Integer)
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
                                 piEntryPoint=SE.DefaultEntryPoint,
                                 piMemoryModel=AM.DefaultMemoryModel,
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
    AS.withOnlineSolver (piSolver pinst) (piFloatMode pinst) ng $ \bak -> do
        let sym = LCB.backendGetSym bak
        (recordFn, _) <- buildRecordLLVMAnnotation
        let ?recordLLVMAnnotation = recordFn
        SL.withBinary path contents Nothing hAlloc sym $ \archInfo _ archVals buildSyscallABI buildFunctionABI _ buildGlobals _ binConf funAbiExt -> DMA.withArchConstraints archInfo $  do
            Just (SL.FunABIExt reg) <- return funAbiExt
            let ?memOpts = LCLM.defaultMemOptions
            let execFeatures = []
            let seConf = SVS.SymbolicExecutionConfig
                     { SVS.secSolver = piSolver pinst
                     , SVS.secLogBranches = False
                     }
            let abiConf = SVS.ABIConfig {
                SVS.abiBuildFunctionABI = buildFunctionABI,
                SVS.abiBuildSyscallABI=buildSyscallABI
            }
            crucProgs <- fmap concat (mapM (ST.translateProgram ng hAlloc) stubProgs) 
            envVarMap <- AEnv.mkEnvVarMap bak (piConcreteEnvVars pinst) (piConcreteEnvVarsFromBytes pinst) (piSymbolicEnvVars pinst)

            -- execute symbolically
            entryPointAddr <- AEp.resolveEntryPointAddrOff binConf $ piEntryPoint pinst
            ambientExecResult <- SVS.symbolicallyExecute' logAction bak hAlloc archInfo archVals seConf execFeatures entryPointAddr (piMemoryModel pinst) buildGlobals (piFsRoot pinst) (piLogFunctionCalls pinst) binConf abiConf (piCommandLineArguments pinst) envVarMap crucProgs
            let crucibleRes = SVS.serCrucibleExecResult ambientExecResult

            --TODO: parameterize: like check in smallPipeline
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
                _ -> return Nothing