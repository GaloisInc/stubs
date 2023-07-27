{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Stubs.SymbolicExecution (
    SymbolicExecutionConfig(..)
  , SymbolicExecutionResult(..)
  , symbolicallyExecute
  , insertFreshGlobals
  , FunctionConfig(..)
  , ABIConfig(..)
  ) where

import           Control.Monad ( foldM )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(..) )
import qualified Control.Monad.State.Strict as CMS
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import           Data.Char as C
import qualified Data.Foldable as F
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as DT
import qualified Data.Traversable as Trav
import qualified Data.Vector as DV
import           GHC.TypeNats ( KnownNat, type (<=) )
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lumberjack as LJ
import qualified System.IO as IO

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.Bytes as LCLB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.Intrinsics as LCLI
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemType as LCLMT
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.EvalStmt as LCSEv
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Types as LCT
import qualified What4.BaseTypes as WT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Diagnostic as AD
import qualified Stubs.Discovery as ADi
import qualified Stubs.Exception as AE
import qualified Stubs.Extensions as AExt
import qualified Stubs.FunctionOverride as AF
import qualified Stubs.FunctionOverride.Extension.Types as AFET
import qualified Stubs.Lift as ALi
import qualified Stubs.Loader.BinaryConfig as ALB
import qualified Stubs.Panic as AP
import qualified Stubs.Solver as AS
import qualified Stubs.Translate as ST
import qualified Stubs.Wrapper as SW
import qualified Stubs.Translate.Core as STC
import qualified Stubs.Preamble as SPR
import qualified Stubs.Common as SC
import qualified Stubs.Memory as SM
import qualified Stubs.Memory.X86_64.Linux ()
import qualified Stubs.Memory.AArch32.Linux ()
import qualified Lang.Crucible.LLVM.Errors as LCLE
import qualified Lang.Crucible.LLVM.MemModel.Partial as LCLMP
import qualified Lang.Crucible.LLVM.MemModel.CallStack as LCLMC
import Stubs.Memory.Common
import qualified Stubs.Extensions as SE
import Data.Data (Typeable)
import Control.Lens ((^.), set)

data SymbolicExecutionConfig arch sym = SymbolicExecutionConfig
  { secSolver :: AS.Solver
  , secLogBranches :: Bool
  -- ^ Report symbolic branches
  }

-- | Results from symbolic execution
data SymbolicExecutionResult arch sym mem=  (SM.IsStubsMemoryModel mem arch) => SymbolicExecutionResult
  { serMemVar :: LCS.GlobalVar (SM.MemType mem arch)
 -- ^ MemVar used in simulation
  , serCrucibleExecResult :: LCS.ExecResult (AExt.AmbientSimulatorState sym arch)
                                            sym
                                            (DMS.MacawExt arch)
                                            (LCS.RegEntry sym (DMS.ArchRegStruct arch))
 -- ^ Crucible execution result
  }

-- | The stack size in bytes
stackSize :: Integer
stackSize = 2 * 1024 * 1024

stackOffset :: Integer
stackOffset = stackSize `div` 2

-- | Heap size in bytes
heapSize :: Integer
heapSize = 2 * 1024 * 1024 * 1024

-- | An execution feature that logs all symbolic branches that occur
sbsFeature :: LJ.LogAction IO AD.Diagnostic
  -> LCSEv.ExecutionFeature p sym ext rtp
sbsFeature logAction = LCSEv.ExecutionFeature $ \case
    LCSE.SymbolicBranchState _pred _tpath _fpath _mergePoint simState -> do
      let loc = simState ^. LCSE.stateLocation
      LJ.writeLog logAction (AD.SymbolicBranch loc)
      return LCSEv.ExecutionFeatureNoChange
    _ -> return LCSEv.ExecutionFeatureNoChange

mkInitialRegVal
  :: (LCB.IsSymInterface sym, DMT.HasRepr (DMC.ArchReg arch) DMT.TypeRepr)
  => DMS.MacawSymbolicArchFunctions arch
  -> sym
  -> DMC.ArchReg arch tp
  -> IO (LCS.RegValue' sym (DMS.ToCrucibleType tp))
mkInitialRegVal symArchFns sym r = do
  let regName = DMS.crucGenArchRegName symArchFns r
  case DMT.typeRepr r of
    DMT.BoolTypeRepr ->
      LCS.RV <$> WI.freshConstant sym regName WT.BaseBoolRepr
    DMT.BVTypeRepr w -> do
      c <- WI.freshConstant sym regName (WT.BaseBVRepr w)
      LCS.RV <$> LCLM.llvmPointer_bv sym c
    DMT.TupleTypeRepr PL.Nil -> return (LCS.RV Ctx.Empty)
    DMT.TupleTypeRepr _ ->
      AP.panic AP.SymbolicExecution "mkInitialRegVal" ["Tuple-typed registers are not supported in initial states: " ++ show regName]
    DMT.FloatTypeRepr {} ->
      AP.panic AP.SymbolicExecution "mkInitialRegVal" ["Float-typed registers are not supported in initial states: " ++ show regName]
    DMT.VecTypeRepr {} ->
      AP.panic AP.SymbolicExecution "mkInitialRegVal" ["Vector-typed registers are not supported in initial states: " ++ show regName]

{-
Note [Resolving concrete syscall numbers and function addresses]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Resolving a syscall number as concrete isn't quite as straightforward as
calling `asBV`. This is because we use the SMT array memory model, if we spill
the value of a syscall number to the stack, then it's not directly possible to
resolve that value as concrete. This is because the value consists of reads
from an SMT array concatenated together.

Instead of using `asBV`, we can query the SMT solver directly to figure out if
a syscall number value is concrete or symbolic. To do so, we.

1. Ask the online solver for a model of the system call number (using
   `checkAndGetModel`), and
2. Send a second query that forbids that model. That is, `assume` that
   bvEq <original-syscall-num-value> <modelled-syscall-num-value> is false,
   and then `check`.

If the second step yields `Unsat`, then we have a concrete syscall number. If
the second step yields `Sat`, however, we have a truly symbolic syscall number.
For now, we fail when given truly symbolic syscall numbers.

All of the same reasoning applies to function addresses, which are resolved in
a similar fashion.
-}

-- | Initialize a list of globals to have fresh symbolic values and insert them
-- into global state.
insertFreshGlobals :: forall sym f
                    . (LCB.IsSymInterface sym, Foldable f)
                   => sym
                   -> f (Some LCS.GlobalVar)
                   -- ^ Collection of global variables to initialize
                   -> LCSG.SymGlobalState sym
                   -- ^ Global state to insert variables into
                   -> IO (LCSG.SymGlobalState sym)
                   -- ^ Updated global state
insertFreshGlobals sym globs initialState = foldM go initialState globs
  where
    go :: LCSG.SymGlobalState sym
       -> Some LCS.GlobalVar
       -> IO (LCSG.SymGlobalState sym)
    go state (Some glob) = do
      let tp = LCS.globalType glob
      let name = DT.unpack (LCS.globalName glob)
      case LCT.asBaseType tp of
        LCT.NotBaseType ->
          case tp of
            LCLM.LLVMPointerRepr w -> do
              -- Create a pointer with symbolic region and offset
              region <- WI.freshNat sym (WI.safeSymbol (name ++ "-region"))
              offset <- WI.freshConstant sym
                                         (WI.safeSymbol (name ++ "-offset"))
                                         (WI.BaseBVRepr w)
              let ptr = LCLM.LLVMPointer region offset
              return $ LCSG.insertGlobal glob ptr state
            _ -> CMC.throwM (AE.UnsuportedGlobalVariableType name tp)
        LCT.AsBaseType bt -> do
          val <- WI.freshConstant sym (WI.safeSymbol name) bt
          return $ LCSG.insertGlobal glob val state

-- | Allocate an @argv@ array for use in a @main(...)@ entry point function.
-- This marshals the list of ByteStrings to an array of C strings. As mandated
-- by section 5.1.2.2.1 of the C standard, the last element of the array will be
-- a null pointer.
--
-- See @Note [Simulating main()]@ in @Options@.
allocaArgv ::
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  LCLM.MemImpl sym ->
  [BS.ByteString] ->
  -- ^ The user-supplied command-line arguments
  IO (LCLM.LLVMPtr sym w, LCLM.MemImpl sym)
allocaArgv bak mem0 argv = do
  let sym = LCB.backendGetSym bak
  let w8 = WI.knownNat @8
  symArgv <-
    Trav.for argv $ \arg ->
    Trav.for (BS.unpack arg) $ \byte ->
    WI.bvLit sym w8 $ BVS.mkBV w8 $ fromIntegral byte
  allocaCStringArray bak mem0 symArgv "argv"

-- | Allocate an @envp@ array for use in a @main(...)@ entry point function.
-- Each environment variable is written in @KEY=VALUE@ format, where the bytes
-- in @VALUE@ may be symbolic. By convention, the last element of the array
-- will be a null pointer.
--
-- See @Note [Simulating main()]@ in @Options@.
allocaEnvp ::
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  LCLM.MemImpl sym ->
  Map.Map BS.ByteString [WI.SymBV sym 8] ->
  -- ^ The user-supplied environment variables
  IO (LCLM.LLVMPtr sym w, LCLM.MemImpl sym)
allocaEnvp bak mem0 envVars = do
  let sym = LCB.backendGetSym bak
  let w8 = WI.knownNat @8
  equalsSign <- WI.bvLit sym w8 $ BVS.mkBV w8 $ toInteger $ C.ord '='
  symEnvVars <-
    Trav.for (Map.toAscList envVars) $ \(key, val) -> do
      key' <- Trav.for (BS.unpack key) $ \byte ->
              WI.bvLit sym w8 $ BVS.mkBV w8 $ fromIntegral byte
      pure $ key' ++ [equalsSign] ++ val
  allocaCStringArray bak mem0 symEnvVars "envp"

-- | Allocate an array of C strings on the stack. The bytes in each C string
-- may be symbolic, but each string will end with a concrete null terminator.
-- The array of strings itself will be terminated with a null pointer.
--
-- See @Note [Simulating main()]@ in @Options@.
allocaCStringArray ::
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  LCLM.MemImpl sym ->
  [[WI.SymBV sym 8]] ->
  -- ^ The sequence of C strings (where each string is represented as a series
  -- of bytes) to turn into an array. Note that none of the strings here are
  -- null-terminated; the null terminators will be added as a part of this
  -- function.
  String ->
  -- ^ A label to describe each string's allocation in the memory model.
  IO (LCLM.LLVMPtr sym w, LCLM.MemImpl sym)
allocaCStringArray bak mem0 cstrs label = do
  let sym = LCB.backendGetSym bak
  let sz = List.genericLength cstrs + 1 -- Note the (+ 1) here for the null pointer
  let ptrWidthBytes = LCLB.bytesToInteger (LCLB.bitsToBytes (WI.intValue ?ptrWidth))
  let szBytes = sz * ptrWidthBytes
  szBytesBV <- WI.bvLit sym ?ptrWidth $ BVS.mkBV ?ptrWidth szBytes
  let loc = "ambient-verifier allocation for " ++ label ++ " array"
  (arrPtr, mem1) <- LCLM.doAlloca bak mem0 szBytesBV LCLD.noAlignment loc
  let memTy = LCLMT.ArrayType (fromIntegral sz) $ LCLMT.PtrType $ LCLMT.MemType $ LCLMT.IntType 8
  let tpr = LCT.VectorRepr $ LCLM.LLVMPointerRepr ?ptrWidth
  sty <- LCLM.toStorableType memTy
  (arr0, mem2) <-
    CMS.runStateT
      (traverse (\cstr -> CMS.StateT $ \mem -> allocaCString bak mem cstr label) cstrs)
      mem1
  nullPtr <- LCLM.mkNullPointer sym ?ptrWidth
  let arr1 = arr0 ++ [nullPtr]
  mem3 <- LCLM.doStore bak mem2 arrPtr tpr sty LCLD.noAlignment $ DV.fromList arr1
  pure (arrPtr, mem3)

-- | Allocate a sequence of bytes (some of which may be symbolic) on the stack
-- as a C string. This adds a concrete null terminator at the end of the
-- string in the process.
--
-- See @Note [Simulating main()]@ in @Options@.
allocaCString ::
  forall sym bak w.
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  LCLM.MemImpl sym ->
  [WI.SymBV sym 8] ->
  -- ^ The bytes to marshal. /Not/ null-terminated.
  String ->
  -- ^ A label to describe each string's allocation in the memory model.
  IO (LCLM.LLVMPtr sym w, LCLM.MemImpl sym)
allocaCString bak mem0 bytes label = do
  let sym = LCB.backendGetSym bak
  let sz = length bytes + 1 -- Note the (+ 1) here for the null terminator
  szBV <- WI.bvLit sym ?ptrWidth $ BVS.mkBV ?ptrWidth $ fromIntegral sz
  let loc = "ambient-verifier allocation for " ++ label ++ " string"
  (strPtr, mem1) <- LCLM.doAlloca bak mem0 szBV LCLD.noAlignment loc
  let w8 = WI.knownNat @8
  let memTy = LCLMT.ArrayType (fromIntegral sz) $ LCLMT.IntType 8
  let tpr = LCT.VectorRepr $ LCLM.LLVMPointerRepr w8
  sty <- LCLM.toStorableType memTy
  bvNullTerminator <- liftIO $ WI.bvLit sym w8 $ BVS.zero w8
  let bytes' = bytes ++ [bvNullTerminator]
  cstr <- Trav.for bytes' $ LCLM.llvmPointer_bv sym
  mem2 <- LCLM.doStore bak mem1 strPtr tpr sty LCLD.noAlignment $ DV.fromList cstr
  pure (strPtr, mem2)
-- | The values of the arguments to the @main()@ function.
-- See @Note [Simulating main()]@ in @Options@.
data MainArgVals sym w = MainArgVals
  { argcVal :: WI.SymBV sym w
  , argvVal :: LCLM.LLVMPtr sym w
  , envpVal :: LCLM.LLVMPtr sym w
  }

-- | Populate the registers corresponding to @main(...)@'s arguments with the
-- user-supplied command line arguments.

-- See @Note [Simulating main()]@ in @Options@.
initMainArguments ::
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , DMS.SymArchConstraints arch
  , w ~ DMC.ArchAddrWidth arch
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  LCLM.MemImpl sym ->
  DMS.GenArchVals DMS.LLVMMemory arch ->
  DMC.ArchReg arch (DMT.BVType w) ->
  -- ^ The register for the first argument (@argc@)
  DMC.ArchReg arch (DMT.BVType w) ->
  -- ^ The register for the second argument (@argv@)
  DMC.ArchReg arch (DMT.BVType w) ->
  -- ^ The register for the third argument (@envp@)
  [BS.ByteString] ->
  -- ^ The user-supplied command-line arguments
  Map.Map BS.ByteString [WI.SymBV sym 8] ->
  -- ^ The user-supplied environment variables
  LCS.RegEntry sym (DMS.ArchRegStruct arch) ->
  -- ^ The initial register state
  IO ( MainArgVals sym w
     , LCS.RegEntry sym (DMS.ArchRegStruct arch)
     , LCLM.MemImpl sym
     )
initMainArguments bak mem0 archVals r0 r1 r2 argv envVars regStruct0 = do
  let sym = LCB.backendGetSym bak
  let argc = List.genericLength argv
  argcBV  <- WI.bvLit sym ?ptrWidth $ BVS.mkBV ?ptrWidth argc
  argcPtr <- LCLM.llvmPointer_bv sym argcBV
  let regStruct1 = DMS.updateReg archVals regStruct0 r0 argcPtr
  (argvPtr, mem1) <- allocaArgv bak mem0 argv
  let regStruct2 = DMS.updateReg archVals regStruct1 r1 argvPtr
  (envpPtr, mem2) <- allocaEnvp bak mem1 envVars
  let regStruct3 = DMS.updateReg archVals regStruct2 r2 envpPtr
  let argVals = MainArgVals
                  { argcVal = argcBV
                  , argvVal = argvPtr
                  , envpVal = envpPtr
                  }
  pure (argVals, regStruct3, mem2)

-- | Configuration parameters concerning functions and overrides
data FunctionConfig arch sym p mem = (SM.IsStubsMemoryModel mem arch) => FunctionConfig {
    fcBuildSyscallABI :: SM.BuildSyscallABI arch sym p mem
  -- ^ Function to construct an ABI specification for system calls
  , fcBuildFunctionABI :: SM.BuildFunctionABI arch sym p mem
  -- ^ Function to construct an ABI specification for function calls
  , fcCrucibleSyntaxOverrides :: AFET.CrucibleSyntaxOverrides (DMC.ArchAddrWidth arch) p sym arch
  -- ^ @crucible-syntax@ overrides to register
  }

data ABIConfig arch sym p mem = (SM.IsStubsMemoryModel mem arch) => ABIConfig {
    abiBuildSyscallABI :: SM.BuildSyscallABI arch sym p mem
  -- ^ Function to construct an ABI specification for system calls
  , abiBuildFunctionABI :: SM.BuildFunctionABI arch sym p mem
  -- ^ Function to construct an ABI specification for function calls
  }

simulateFunction
  :: forall m arch ext sym bak binFmt w scope st fs solver p.
  ( CMC.MonadThrow m
     , MonadIO m
     , ext ~ DMS.MacawExt arch
     , LCCE.IsSyntaxExtension ext
     , LCB.IsSymBackend sym bak
     , DMB.BinaryLoader arch binFmt
     , DMS.SymArchConstraints arch
     , w ~ DMC.ArchAddrWidth arch
     , 16 <= w
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , LCB.IsSymBackend sym bak
     , WPO.OnlineSolver solver
     , p ~ AExt.AmbientSimulatorState sym arch
     , SM.IsStubsMemoryModel DMS.LLVMMemory arch,
     ?memOpts::LCLM.MemOptions
     , ?recordLLVMAnnotation::LCLMC.CallStack -> LCLMP.BoolAnn sym-> LCLE.BadBehavior sym -> IO ()
     , LCS.RegValue sym (SM.MemType DMS.LLVMMemory arch) ~ LCLM.MemImpl sym
     , STC.StubsArch arch
  , SPR.Preamble arch
  , SM.PtrType DMS.LLVMMemory arch ~ LCLM.LLVMPointerType (DMC.ArchAddrWidth arch)
  , SM.MemType DMS.LLVMMemory arch ~ LCLM.Mem
  , Typeable arch
  ,SM.VerifierState sym DMS.LLVMMemory arch ~ SE.AmbientSimulatorState sym arch
  ,WI.IsExprBuilder sym, WI.IsSymExprBuilder sym
  , 1 <= DMC.ArchAddrWidth arch
  , DMM.MemWidth (DMC.ArchAddrWidth arch)
  , 16 <= DMC.ArchAddrWidth arch
     )
  => LJ.LogAction IO AD.Diagnostic
  -> bak
  -> [LCS.GenericExecutionFeature sym]
  -> LCF.HandleAllocator
  -> DMA.ArchitectureInfo arch
  -> DMS.ArchVals arch
  -> SymbolicExecutionConfig arch sym
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -> DMC.ArchSegmentOff arch
  -- ^ The address of the entry point function
  -> ALB.BinaryConfig arch binFmt
  -- ^ Information about the loaded binaries
  -> ABIConfig arch sym p DMS.LLVMMemory
  -- ^ Configuration parameters concerning functions and overrides
  -> [BS.ByteString]
  -- ^ The user-supplied command-line arguments
  -> Map.Map BS.ByteString [WI.SymBV sym 8]
  -- ^ The user-supplied environment variables
  -> [ST.CrucibleProgram arch]
  -> m (SymbolicExecutionResult arch sym DMS.LLVMMemory)
simulateFunction logAction bak execFeatures halloc archInfo archVals seConf initialMem entryPointAddr binConf fnConf cliArgs envVars crProgs = do
  let sym = LCB.backendGetSym bak
  let symArchFns = DMS.archFunctions archVals
  let crucRegTypes = DMS.crucArchRegTypes symArchFns
  let regsRepr = LCT.StructRepr crucRegTypes

  -- Set up an initial register state (mostly symbolic, with an initial stack)
  --
  -- Put the stack pointer in the middle of our allocated stack so that both sides can be addressed
  initialRegs <- liftIO $ DMS.macawAssignToCrucM (mkInitialRegVal symArchFns sym) (DMS.crucGenRegAssignment symArchFns)
  stackInitialOffset <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackOffset)
  sp <- liftIO $ SM.genStackPtr @DMS.LLVMMemory @arch @_ @sym (SM.imStackBasePtr initialMem) stackInitialOffset (SC.Sym sym bak)
  let initialRegsEntry = LCS.RegEntry regsRepr initialRegs
  let regsWithStack = SM.insertStackPtr archVals sp initialRegsEntry

  let ?ptrWidth = WI.knownRepr
  let globals0 = SM.imGlobals initialMem

  environGlob <- liftIO $
    LCCC.freshGlobalVar halloc
                        (DT.pack "AMBIENT_environ")
                        (SM.ptrRepr @DMS.LLVMMemory @arch)

  let tsym = SC.Sym (LCB.backendGetSym bak) bak
  -- Create primary overrides
  ovs <- liftIO $ mapM (SW.crucibleProgramToFunctionOverride tsym ) crProgs
  -- Create Startup overrides : TODO check validity somwhere
  initOvs <- liftIO $ mapM (SW.genInitHooks tsym ) crProgs
  initCOvs <- liftIO $ mapM (SW.genInitOvHooks tsym) crProgs
  let SM.BuildSyscallABI buildSyscallABI = abiBuildSyscallABI fnConf
  let syscallABI = buildSyscallABI initialMem (ALB.bcUnsuportedRelocations binConf)
  let SM.BuildFunctionABI buildFunctionABI = abiBuildFunctionABI fnConf 
  let functionABI = buildFunctionABI AF.TestContext initialMem archVals
                                     (ALB.bcUnsuportedRelocations binConf)
                                     mempty
                                     ovs
                                     [Some environGlob]

  let mem0 = case LCSG.lookupGlobal (SM.imMemVar initialMem) globals0 of
               Just mem -> mem
               Nothing  -> AP.panic AP.FunctionOverride "simulateFunction"
                             [ "Failed to find global variable for memory: "
                               ++ show (LCCC.globalName (SM.imMemVar initialMem)) ]
  (mainReg0, mainReg1, mainReg2) <-
    case SM.functionIntegerArgumentRegisters functionABI of
      (reg0:reg1:reg2:_) -> pure (reg0, reg1, reg2)
      _ -> AP.panic AP.SymbolicExecution "simulateFunction"
             [ "Not enough registers for the main() function" ]
  (mainArgVals, regsWithMainArgs, mem1) <- liftIO $
    initMainArguments bak mem0 archVals mainReg0 mainReg1 mainReg2 cliArgs envVars regsWithStack
  let globals2 = LCSG.insertGlobal (SM.imMemVar initialMem) mem1 $
                 LCSG.insertGlobal environGlob (envpVal mainArgVals) globals0
  let arguments = LCS.RegMap (Ctx.singleton regsWithMainArgs)

  let mainBinaryPath = ALB.mainLoadedBinaryPath binConf
  Some discoveredEntry <- ADi.discoverFunction logAction archInfo mainBinaryPath entryPointAddr
  LCCC.SomeCFG cfg <- ALi.liftDiscoveredFunction halloc (ALB.lbpPath mainBinaryPath)
                                                 (DMS.archFunctions archVals) discoveredEntry
  let simAction = LCS.runOverrideSim regsRepr $ do
                    -- First, initialize the symbolic file system...

                    -- ...then simulate any startup overrides...
                    F.traverse_ (\ov -> AF.functionOverride ov
                                                            bak
                                                            Ctx.Empty
                                                            dummyGetVarArg
                                                            -- NOTE: Startup
                                                            -- overrides cannot
                                                            -- currently call
                                                            -- into parent
                                                            -- overrides
                                                            [])
                                (concat initCOvs)
                    -- ...then simulate any startup overrides...
                    F.traverse_ (\ov  -> AF.functionOverride ov
                                                            bak
                                                            Ctx.Empty
                                                            dummyGetVarArg
                                                            -- NOTE: Startup
                                                            -- overrides cannot
                                                            -- currently call
                                                            -- into parent
                                                            -- overrides
                                                            [])
                                (concat initOvs)
                    -- ...and finally, run the entrypoint function.
                    LCS.regValue <$> LCS.callCFG cfg arguments

  DMS.withArchEval archVals sym $ \archEvalFn -> do
    extImpl <- SM.genExtImpl @DMS.LLVMMemory tsym initialMem archEvalFn halloc archVals archInfo binConf functionABI syscallABI
    -- Register any externs, auxiliary functions, forward declarations used in
    -- the startup overrides.
    (startupBindings, globals4) <-
      F.foldlM (\(bindings, globals) functionOv ->
                 liftIO $ insertFunctionOverrideReferences
                            bak functionABI functionOv bindings globals)
               (LCF.emptyHandleMap, globals2)
               []
    -- Also register the entry point function, as we will not be able to start
    -- simulation without it.
    let bindings = LCF.insertHandleMap (LCCC.cfgHandle cfg)
                                       (LCS.UseCFG cfg (LCAP.postdomInfo cfg))
                                       startupBindings
    let ambientSimState = set AExt.discoveredFunctionHandles
                          (Map.singleton entryPointAddr (LCCC.cfgHandle cfg))
                          AExt.emptyAmbientSimulatorState
    -- Note: the 'Handle' here is the target of any print statements in the
    -- Crucible CFG; we shouldn't have any, but if we did it would be better to
    -- capture the output over a pipe.
    let ctx = LCS.initSimContext bak (MapF.union LCLI.llvmIntrinsicTypes LCLS.llvmSymIOIntrinsicTypes) halloc IO.stdout (LCS.FnBindings bindings) extImpl  ambientSimState
    let s0 = LCS.InitialState ctx globals4 LCS.defaultAbortHandler regsRepr simAction
    let sbsRecorder = sbsFeature logAction
    let executionFeatures = [sbsRecorder | secLogBranches seConf] ++ fmap LCS.genericToExecutionFeature execFeatures

    res <- liftIO $ LCS.executeCrucible executionFeatures s0
    return $ SymbolicExecutionResult (SM.imMemVar initialMem)
                                     res
  where
    -- Syntax overrides cannot make use of variadic arguments, so if this
    -- callback is ever used, something has gone awry.
    dummyGetVarArg :: AF.GetVarArg sym
    dummyGetVarArg = AF.GetVarArg $ \_ ->
      AP.panic AP.SymbolicExecution "simulateFunction"
        ["A startup override cannot use variadic arguments"]


symbolicallyExecute
  ::  ( CMC.MonadThrow m
     , MonadIO m
     , LCB.IsSymBackend sym bak
     , LCCE.IsSyntaxExtension (DMS.MacawExt arch)
     , ext ~ DMS.MacawExt arch
     , LCCE.IsSyntaxExtension ext
     , DMB.BinaryLoader arch binFmt
     , DMS.SymArchConstraints arch
     , w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , 16 <= w
     , KnownNat w
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , ?memOpts :: LCLM.MemOptions
     , LCLM.HasLLVMAnn sym
     , SM.IsStubsMemoryModel DMS.LLVMMemory arch
     , STC.StubsArch arch
  , SPR.Preamble arch
  , SM.PtrType DMS.LLVMMemory arch ~ LCLM.LLVMPointerType (DMC.ArchAddrWidth arch)
  , SM.MemType DMS.LLVMMemory arch ~ LCLM.Mem
  , Typeable arch
  ,SM.VerifierState sym DMS.LLVMMemory arch ~ SE.AmbientSimulatorState sym arch
  ,WI.IsExprBuilder sym, WI.IsSymExprBuilder sym
  , 1 <= DMC.ArchAddrWidth arch
  , DMM.MemWidth (DMC.ArchAddrWidth arch)
  , 16 <= DMC.ArchAddrWidth arch
     )
  => LJ.LogAction IO AD.Diagnostic
  -> bak
  -> LCF.HandleAllocator
  -> DMA.ArchitectureInfo arch
  -> DMS.ArchVals arch
  -> SymbolicExecutionConfig arch sym
  -> [LCS.GenericExecutionFeature sym]
  -> DMC.ArchSegmentOff arch
  -- ^ The address of the entry point function
  -> ALB.BinaryConfig arch binFmt
  -- ^ Information about the loaded binaries
  -> ABIConfig arch sym (SE.AmbientSimulatorState sym arch) DMS.LLVMMemory
  -- ^ Configuration parameters concerning functions and overrides
  -> [BS.ByteString]
  -- ^ The user-supplied command-line arguments
  -> Map.Map BS.ByteString [WI.SymBV sym 8]
  -- ^ The user-supplied environment variables
  -> [ST.CrucibleProgram arch]
  -> m (SymbolicExecutionResult arch sym DMS.LLVMMemory)
symbolicallyExecute logAction bak halloc archInfo archVals seConf execFeatures entryPointAddr binConf fnConf cliArgs envVars crucProgs= do
  initialMem <- SM.initMem (SC.Sym (LCB.backendGetSym bak) bak) archInfo stackSize binConf halloc
  simulateFunction logAction bak execFeatures halloc archInfo archVals seConf initialMem entryPointAddr binConf fnConf cliArgs envVars crucProgs
