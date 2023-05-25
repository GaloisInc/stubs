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
{-# LANGUAGE ViewPatterns #-}
module Stubs.SymbolicExecution (
    SymbolicExecutionConfig(..)
  , SymbolicExecutionResult(..)
  , symbolicallyExecute
  , insertFreshGlobals
  , initializeMemory
  , FunctionConfig(..)
  , extractIP
  , lookupFunction
  , resolveFuncAddrFromBinaries
  , insertFunctionHandle
  ) where

import           Control.Lens ( Lens', (^.), (&), (.~), set, over )
import           Control.Monad ( foldM )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(..) )
import qualified Control.Monad.State.Strict as CMS
import qualified Data.BinarySymbols as BinSym
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import           Data.Char as C
import qualified Data.Foldable as F
import qualified Data.IntMap as IM
import           Data.IORef ( readIORef )
import qualified Data.List as List
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe, isJust )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as DT
import qualified Data.Traversable as Trav
import qualified Data.Vector as DV
import qualified Data.Vector.NonEmpty as NEV
import           GHC.TypeNats ( KnownNat, type (<=) )
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lumberjack as LJ
import qualified Prettyprinter as PP
import qualified System.FilePath as SF
import qualified System.IO as IO

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.BinaryLoader.ELF as DMBE
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Memory as DMSM
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
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LCLMP
import qualified Lang.Crucible.LLVM.MemType as LCLMT
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.EvalStmt as LCSEv
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Simulator.OverrideSim as LCSO
import qualified Lang.Crucible.SymIO as LCSy
import qualified Lang.Crucible.SymIO.Loader as LCSL
import qualified Lang.Crucible.Types as LCT
import qualified What4.BaseTypes as WT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP
import qualified What4.Protocol.Online as WPO
import qualified What4.Symbol as WSym

import qualified Stubs.Diagnostic as AD
import qualified Stubs.Discovery as ADi
import qualified Stubs.Exception as AE
import qualified Stubs.Extensions as AExt
import qualified Stubs.Extensions.Memory as AEM
import qualified Stubs.FunctionOverride as AF
import qualified Stubs.FunctionOverride.Extension.Types as AFET
import qualified Stubs.FunctionOverride.Overrides.ForwardDeclarations as AFOF
import qualified Stubs.Lift as ALi
import qualified Stubs.Loader.BinaryConfig as ALB
import qualified Stubs.Loader.LoadOptions as ALL
import qualified Stubs.Loader.Relocations as ALR
import qualified Stubs.Loader.Versioning as ALV
import qualified Stubs.Memory as AM
import qualified Stubs.Panic as AP
import qualified Stubs.Solver as AS
import qualified Stubs.Syscall as ASy
import qualified Stubs.Verifier.Concretize as AVC

data SymbolicExecutionConfig arch sym = SymbolicExecutionConfig
  { secSolver :: AS.Solver
  , secLogBranches :: Bool
  -- ^ Report symbolic branches
  }

-- | Results from symbolic execution
data SymbolicExecutionResult arch sym = SymbolicExecutionResult
  { serMemVar :: LCS.GlobalVar LCLM.Mem
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

-- | Extract the instruction pointer from a register assignment.  This function
-- concretizes the instruction pointer and throws an
-- 'AE.ConcretizationFailedUnknown' or 'AE.ConcretizationFailedSymbolic'
-- exception if the instruction pointer cannot be concretized.
extractIP
  :: forall bak mem arch sym solver scope st fs
   . ( bak ~ LCBO.OnlineBackend solver scope st fs
     , sym ~ WE.ExprBuilder scope st fs
     , DMS.SymArchConstraints arch
     , LCB.IsSymBackend sym bak
     , WPO.OnlineSolver solver
     )
  => bak
  -> DMS.GenArchVals mem arch
  -> Ctx.Assignment (LCS.RegValue' sym)
                    (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
  -- ^ Registers to extract IP from
  -> IO Integer
extractIP bak archVals regs = do
  let regsEntry = LCS.RegEntry regsRepr regs
  let offset = LCLMP.llvmPointerOffset $ LCS.regValue
                                       $ DMS.lookupReg archVals regsEntry DMC.ip_reg
  resolveConcreteStackVal bak (Proxy @arch) AE.FunctionAddress offset
  where
    symArchFns :: DMS.MacawSymbolicArchFunctions arch
    symArchFns = DMS.archFunctions archVals

    crucRegTypes :: Ctx.Assignment LCT.TypeRepr (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
    crucRegTypes = DMS.crucArchRegTypes symArchFns

    regsRepr :: LCT.TypeRepr (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
    regsRepr = LCT.StructRepr crucRegTypes

-- | This function is used to look up a function handle when a call is
-- encountered during symbolic execution. See also @wmeLookupFunction@ in
-- "Ambient.Verifier.WME", which constructs function CFGs in a slightly
-- different way in order to be able to jump into the middle of functions.
symExLookupFunction :: forall sym bak arch binFmt p ext w scope solver st fs args ret mem
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , LCCE.IsSyntaxExtension ext
     , DMB.BinaryLoader arch binFmt
     , DMS.SymArchConstraints arch
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , p ~ AExt.AmbientSimulatorState sym arch
     , ext ~ DMS.MacawExt arch
     , w ~ DMC.ArchAddrWidth arch
     , args ~ (LCT.EmptyCtx LCT.::>
               LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
     , ret ~ LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
     , WPO.OnlineSolver solver
     )
   => LJ.LogAction IO AD.Diagnostic
   -> bak
   -> AM.InitialMemory sym w
   -> DMS.GenArchVals mem arch
   -> ALB.BinaryConfig arch binFmt
   -- ^ Information about the loaded binaries
   -> AF.FunctionABI arch sym p
   -- ^ Function call ABI specification for 'arch'
   -> LCF.HandleAllocator
   -> DMA.ArchitectureInfo arch
   -> Maybe FilePath
   -- ^ Optional path to the file to log function calls to
   -> DMS.LookupFunctionHandle p sym arch
symExLookupFunction logAction bak initialMem archVals binConf abi hdlAlloc archInfo mFnCallLog=
  lookupFunction buildCfg logAction bak initialMem archVals binConf abi hdlAlloc mFnCallLog
  where
    buildCfg :: DMM.MemSegmentOff w
             -- ^ The address offset
             -> ALB.LoadedBinaryPath arch binFmt
             -- ^ The binary that the address resides in
             -> IO (LCCC.SomeCFG ext args ret)
    buildCfg funcAddrOff bin = do
      Some discoveredEntry <- ADi.discoverFunction logAction archInfo bin funcAddrOff
      ALi.liftDiscoveredFunction hdlAlloc (ALB.lbpPath bin)
                                 (DMS.archFunctions archVals) discoveredEntry

-- | The workhorse for 'symExLookupFunction' and @wmeLookupFunction@ (in
-- "Ambient.Verifier.WME").
--
-- NOTE: This currently only works for concrete function addresses, but once
-- https://github.com/GaloisInc/crucible/pull/615 lands, we should update it to
-- return a mux of all possible targets.
lookupFunction :: forall sym bak arch binFmt p ext w scope solver st fs args ret mem
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , LCCE.IsSyntaxExtension ext
     , DMB.BinaryLoader arch binFmt
     , DMS.SymArchConstraints arch
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , p ~ AExt.AmbientSimulatorState sym arch
     , ext ~ DMS.MacawExt arch
     , w ~ DMC.ArchAddrWidth arch
     , args ~ (LCT.EmptyCtx LCT.::>
               LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
     , ret ~ LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
     , WPO.OnlineSolver solver
     )
   => (DMM.MemSegmentOff w -> ALB.LoadedBinaryPath arch binFmt -> IO (LCCC.SomeCFG ext args ret))
   -- ^ How to construct a CFG for a function (given its address offset and
   -- binary) in the event that an override for the function cannot be found.
   -> LJ.LogAction IO AD.Diagnostic
   -> bak
   -> AM.InitialMemory sym w
   -> DMS.GenArchVals mem arch
   -> ALB.BinaryConfig arch binFmt
   -- ^ Information about the loaded binaries
   -> AF.FunctionABI arch sym p
   -- ^ Function call ABI specification for 'arch'
   -> LCF.HandleAllocator
   -> Maybe FilePath
   -- ^ Optional path to the file to log function calls to
   -> DMS.LookupFunctionHandle p sym arch
lookupFunction buildCfg logAction bak initialMem archVals binConf abi hdlAlloc mFnCallLog =
  DMS.LookupFunctionHandle $ \state0 _mem regs -> do
    -- Extract instruction pointer value and look the address up in
    -- 'addressToFnHandle'
    funcAddr <- fromIntegral <$> extractIP bak archVals regs
    (hdl, state1) <- lookupHandle funcAddr state0

    -- Record function event and emit a diagnostic
    let hdlName = LCF.handleName hdl
    mbReturnAddr <-
      -- Checking the return address requires consulting an SMT solver, and the
      -- time it takes to do this could add up. We only care about this
      -- information when --log-function-calls is enabled, so we skip this step
      -- if that option is disabled.
      if isJust mFnCallLog
      then let mem = readGlobal (AM.imMemVar initialMem) state1 in
           AF.functionReturnAddr abi bak archVals regs mem
      else pure Nothing
    LJ.writeLog logAction $
      AD.FunctionCall hdlName funcAddr mbReturnAddr

    pure (hdl, state1)

  where
    symArchFns :: DMS.MacawSymbolicArchFunctions arch
    symArchFns = DMS.archFunctions archVals

    crucRegTypes :: Ctx.Assignment LCT.TypeRepr (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
    crucRegTypes = DMS.crucArchRegTypes symArchFns

    regsRepr :: LCT.TypeRepr ret
    regsRepr = LCT.StructRepr crucRegTypes

    -- This function abstracts over a common pattern when dealing with lazily
    -- registering overrides (Note [Lazily registering overrides] in A.Extensions):
    --
    -- (1) First, check to see if the function has had an override registered
    --     previously by looking in the appropriate spot in the
    --     AmbientSimulatorState. If so, just use that handle.
    -- (2) If not, check to see if the user supplied an override for this
    --     function by looking in the appropriate spot in the FunctionABI.
    --     If so, register that override, allocate a new handle for it, and
    --     return that handle.
    -- (3) If not, perform some other action.
    lazilyRegisterHandle ::
         forall key rtp blocks r ctx
       . Ord key
      => LCS.CrucibleState p sym ext rtp blocks r ctx
      -> key
         -- ^ The type of function. This can be a MemWord (for kernel-specific
         --   functions) or a FunctionName (for other kinds of functions).
      -> Lens' (AExt.AmbientSimulatorState sym arch)
               (Map.Map key (AF.FunctionOverrideHandle arch))
         -- ^ A lens into the corresponding field of AmbientSimulatorState.
         --   This is used both in step (1), for checking if the key is
         --   present, and in step (2), for updating the state when
         --   registering the override.
      -> Map.Map key (NEL.NonEmpty (AF.SomeFunctionOverride p sym arch))
         -- ^ A Map (contained in the FunctionABI) that contains user-supplied
         --   overrides.
      -> IO ( LCF.FnHandle args ret
            , LCS.CrucibleState p sym ext rtp blocks r ctx
            )
         -- The action to perform in step (3).
      -> IO ( LCF.FnHandle args ret
            , LCS.CrucibleState p sym ext rtp blocks r ctx
            )
         -- The function handle to use, as well as the updated state.
    lazilyRegisterHandle state key ovHandlesL fnAbiMap noFnFoundInAbiMap = do
      -- Step (1)
      case Map.lookup key (state ^. LCS.stateContext . LCS.cruciblePersonality . ovHandlesL) of
        Just handle -> pure (handle, incrementOvsApplied state)
        Nothing ->
          -- Step (2)
          case Map.lookup key fnAbiMap of
            Just ((AF.SomeFunctionOverride fnOverride) NEL.:| parents) -> do
              (handle, state') <- mkAndBindOverride state fnOverride parents
              let state'' = over (LCS.stateContext . LCS.cruciblePersonality . ovHandlesL)
                                 (Map.insert key handle)
                                 state'
              pure (handle, incrementOvsApplied state'')
            Nothing -> -- Step (3)
                       noFnFoundInAbiMap

    -- Increment the count of overrides applied in a crucible state
    incrementOvsApplied :: LCS.CrucibleState p sym ext rtp blocks r ctx
                        -> LCS.CrucibleState p sym ext rtp blocks r ctx
    incrementOvsApplied = AExt.incrementSimStat AExt.lensNumOvsApplied

    -- Look up a function handle from an address.  Performs the lookup in the
    -- following order:
    --
    -- (1) Check for an override for the address at a fixed address in kernel
    --     memory.  If not found, proceed to (2).
    -- (2) If the address points to a PLT stub:
    --
    --     (a) If the PLT stub name has an override, dispatch the override.
    --     (b) If not, determine the address that the PLT stub jumps to
    --         and proceed to (3) with the new address.
    --
    --     If the address does not point to a PLT stub, proceed to (3).
    -- (3) Check for an user-specified override for the given address in an
    --     @overrides.yaml@ file. If not found, proceed to (4).
    -- (4) Look up the function names corresponding to the address. If an
    --     override is registered to one of those names, dispatch the override.
    --     Otherwise, proceed to (5).
    -- (5) Perform incremental code discovery on the function at the address
    --     (see Note [Incremental code discovery] in A.Extensions) and return
    --     the resulting function handle, caching it in the process.
    --
    -- In each of steps (1)–(5), we check at the beginning to see if the
    -- function's handle has been registered previously. If so, we just use
    -- that. We only allocate a new function handle if it has not been
    -- registered before.
    -- See Note [Lazily registering overrides] in A.Extensions.
    lookupHandle
      :: forall rtp blocks r ctx
       . DMM.MemWord w
      -> LCS.CrucibleState p sym ext rtp blocks r ctx
      -> IO ( LCF.FnHandle args ret
            , LCS.CrucibleState p sym ext rtp blocks r ctx
            )
    lookupHandle funcAddr state =
      -- Step (1)
      lazilyRegisterHandle state
                           (AF.AddrFromKernel funcAddr)
                           AExt.functionAddrOvHandles
                           (AF.functionAddrMapping abi) $
        -- Step (2)
        case Map.lookup funcAddr (ALB.bcPltStubs binConf) of
          -- If 'funcAddr' points to a PLT stub, dispatch an override.
          -- Otherwise continue resolving the function address.
          Just pltStubVersym ->
            -- Step (2)(a)
            --
            -- NB: When looking up overrides, we only consult the function name
            -- and completely ignore the version. In the future, we will want
            -- to allow users to specify overrides that only apply to
            -- particular versions. See #104.
            lazilyRegisterHandle state
                                 (ALV.versymSymbol pltStubVersym)
                                 AExt.functionOvHandles
                                 (AF.functionNameMapping abi) $ do
              -- Step (2)(b)
              (funcAddrOff, bin) <- resolvePLTStub pltStubVersym
              dispatchFuncAddrOff funcAddr funcAddrOff bin state
          Nothing -> do
            (funcAddrOff, bin) <- resolveFuncAddrAndBin funcAddr
            dispatchFuncAddrOff funcAddr funcAddrOff bin state

    -- Resolve the address that a PLT stub will jump to, also returning the
    -- binary that the address resides in (see
    -- @Note [Address offsets for shared libraries]@ in A.Loader.LoadOffset).
    resolvePLTStub ::
      ALV.VersionedFunctionName ->
      IO (DMM.MemSegmentOff w, ALB.LoadedBinaryPath arch binFmt)
    resolvePLTStub pltStubVersym =
      case Map.lookup pltStubVersym (ALB.bcDynamicFuncSymbolMap binConf) of
        Just funcAddr -> resolveFuncAddrAndBin funcAddr
        Nothing -> CMC.throwM (AE.UnhandledPLTStub pltStubVersym)

    -- Resolve an address offset, also returning the binary that the address
    -- resides in (see @Note [Address offsets for shared libraries]@ in
    -- A.Loader.LoadOffset).
    resolveFuncAddrAndBin ::
      DMM.MemWord w ->
      IO (DMM.MemSegmentOff w, ALB.LoadedBinaryPath arch binFmt)
    resolveFuncAddrAndBin funcAddr = do
      (funcAddrOff, binIndex) <- resolveFuncAddrFromBinaries binConf funcAddr
      let loadedBinaryPath = ALB.bcBinaries binConf NEV.! binIndex
      pure (funcAddrOff, loadedBinaryPath)

    -- This corresponds to steps (3) and (4) in lookupHandle's documentation.
    -- Any indirections by way of PLT stubs should be resolved by this point.
    dispatchFuncAddrOff ::
      DMM.MemWord w ->
      DMM.MemSegmentOff w ->
      -- ^ The address offset
      ALB.LoadedBinaryPath arch binFmt ->
      -- ^ The binary that the address resides in
      LCS.CrucibleState p sym ext rtp blocks r ctx ->
      IO ( LCF.FnHandle args ret
         , LCS.CrucibleState p sym ext rtp blocks r ctx
         )
    dispatchFuncAddrOff funcAddr funcAddrOff bin state =
      -- Step (3)
      --
      -- Note that we call `takeFileName` on the binary path since the
      -- @overrides.yaml@ file only cares about the file name, not the full path.
      lazilyRegisterHandle state
                           (AF.AddrInBinary funcAddr (SF.takeFileName (ALB.lbpPath bin)))
                           AExt.functionAddrOvHandles
                           (AF.functionAddrMapping abi) $
      -- Step (4)
      case Map.lookup funcAddrOff (ALB.lbpEntryPoints bin) of
        Just fnVersyms ->
          -- Look up each of the symbol names associated with each address.
          -- If we find a handle for one of the names, stop searching and
          -- return that handle. Otherwise, fall back on 'lookupOrDiscoverFuncAddrOff'.
          let findHandleForSym fnSym findNextSym =
                lazilyRegisterHandle state fnSym
                                     AExt.functionOvHandles
                                     (AF.functionNameMapping abi)
                                     findNextSym in
          let fallback = lookupOrDiscoverFuncAddrOff funcAddrOff bin state in
          -- NB: When looking up overrides, we only consult the function name
          -- and completely ignore the version. In the future, we will want
          -- to allow users to specify overrides that only apply to
          -- particular versions. See #104.
          foldr findHandleForSym fallback (fmap ALV.versymSymbol fnVersyms)
        Nothing ->
          lookupOrDiscoverFuncAddrOff funcAddrOff bin state

    -- Look up the function handle for an address offset, performing code
    -- discovery if the address has not yet been encountered before.
    -- See Note [Incremental code discovery] in A.Extensions.
    --
    -- This corresponds to step (5) in lookupHandle's docs
    lookupOrDiscoverFuncAddrOff ::
      DMM.MemSegmentOff w ->
      -- ^ The address offset
      ALB.LoadedBinaryPath arch binFmt ->
      -- ^ The binary that the address resides in
      LCS.CrucibleState p sym ext rtp blocks r ctx ->
      IO ( LCF.FnHandle args ret
         , LCS.CrucibleState p sym ext rtp blocks r ctx
         )
    lookupOrDiscoverFuncAddrOff funcAddrOff bin state0 = do
      (hdl, state3) <- case Map.lookup funcAddrOff (state0 ^. LCS.stateContext . LCS.cruciblePersonality . AExt.discoveredFunctionHandles) of
        Just handle -> pure (handle, state0)
        Nothing -> do
          LCCC.SomeCFG cfg <- buildCfg funcAddrOff bin
          let cfgHandle = LCCC.cfgHandle cfg
          let state1 = insertFunctionHandle state0 cfgHandle (LCS.UseCFG cfg (LCAP.postdomInfo cfg))
          let state2 = over (LCS.stateContext . LCS.cruciblePersonality . AExt.discoveredFunctionHandles)
                            (Map.insert funcAddrOff cfgHandle)
                            state1
          pure (LCCC.cfgHandle cfg, state2)
      pure (hdl, state3)

    mkAndBindOverride :: forall fnArgs fnRet rtp blocks r ctx
                       . LCS.CrucibleState p sym ext rtp blocks r ctx
                      -> AF.FunctionOverride p sym fnArgs arch fnRet
                      -> [ AF.SomeFunctionOverride p sym arch ]
                      -> IO ( LCF.FnHandle args ret
                            , LCS.CrucibleState p sym ext rtp blocks r ctx
                            )
    mkAndBindOverride state0 fnOverride parents = do
      -- First, construct an override for the function.
      let retOV :: forall r'
                 . LCSO.OverrideSim p sym ext r' args ret
                                   (Ctx.Assignment (LCS.RegValue' sym)
                                                   (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
          retOV = do
            mem <- LCS.readGlobal $ AM.imMemVar initialMem
            argMap <- LCS.getOverrideArgs
            let argReg = massageRegAssignment $ LCS.regMap argMap
            (args, getVarArg) <- liftIO $
              AF.functionIntegerArguments abi bak
                                          (AF.functionArgTypes fnOverride)
                                          argReg mem
            retVal <- AF.functionOverride fnOverride bak args getVarArg parents
            AF.functionIntegerReturnRegisters abi bak archVals
                                                (AF.functionReturnType fnOverride)
                                                retVal
                                                argReg

      let ov :: LCSO.Override p sym ext args ret
          ov = LCSO.mkOverride' (AF.functionName fnOverride) regsRepr retOV

      -- Next, register any externs, auxiliary functions, or forward
      -- declarations that are used in the override.
      let LCS.FnBindings curHandles = state0 ^. LCS.stateContext ^. LCS.functionBindings
      let curGlobals = state0 ^. LCSE.stateGlobals
      (newHandles, newGlobals) <-
        insertFunctionOverrideReferences bak abi fnOverride curHandles curGlobals
      let state1 = state0 & LCS.stateContext . LCS.functionBindings
                              .~ LCS.FnBindings newHandles
                          & LCSE.stateGlobals
                              .~ newGlobals
      -- Finally, build a function handle for the override and insert it into
      -- the state.
      bindOverrideHandle state1 hdlAlloc (Ctx.singleton regsRepr) crucRegTypes ov

    -- Massage the RegEntry Assignment that getOverrideArgs provides into the
    -- form that FunctionABI expects.
    massageRegAssignment ::
         Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx LCT.::> LCT.StructType ctx)
      -> Ctx.Assignment (LCS.RegValue' sym) ctx
    massageRegAssignment = LCS.unRV . Ctx.last . FC.fmapFC (LCS.RV . LCS.regValue)

    readGlobal ::
      forall tp rtp blocks r ctx.
      LCS.GlobalVar tp ->
      LCS.CrucibleState p sym ext rtp blocks r ctx ->
      LCS.RegValue sym tp
    readGlobal gv st = do
      let globals = st ^. LCSE.stateTree . LCSE.actFrame . LCS.gpGlobals
      case LCSG.lookupGlobal gv globals of
        Just v  -> v
        Nothing -> AP.panic AP.SymbolicExecution "lookupFunction"
                     [ "Failed to find global variable: "
                       ++ show (LCCC.globalName gv) ]

-- | This function builds a function handle for an override and inserts it into
-- a state's function bindings
bindOverrideHandle :: MonadIO m
                   => LCS.SimState p sym ext r f a
                   -- ^ State to insert function handle into
                   -> LCF.HandleAllocator
                   -> Ctx.Assignment LCT.TypeRepr args
                   -- ^ Types of arguments to override
                   -> LCT.CtxRepr ctx
                   -- ^ Override return type
                   -> LCSO.Override p sym ext args (LCT.StructType ctx)
                   -- ^ Override to build binding for
                   -> m ( LCF.FnHandle args (LCT.StructType ctx)
                       -- New function handle for override
                        , LCS.SimState p sym ext r f a)
                       -- ^ Updated state containing new function handle
bindOverrideHandle state hdlAlloc atps rtps ov = do
  handle <- liftIO $ LCF.mkHandle' hdlAlloc
                                   (LCS.overrideName ov)
                                   atps
                                   (LCT.StructRepr rtps)
  return (handle, insertFunctionHandle state handle (LCS.UseOverride ov))

-- | Insert a function handle into a state's function bindings
insertFunctionHandle :: LCS.SimState p sym ext r f a
                   -- ^ State to update
                   -> LCF.FnHandle args ret
                   -- ^ Handle to bind and insert
                   -> LCS.FnState p sym ext args ret
                   -- ^ Function state to bind handle to
                   -> LCS.SimState p sym ext r f a
insertFunctionHandle state handle fnState =
  let LCS.FnBindings curHandles = state ^. LCS.stateContext ^. LCS.functionBindings in
  let newHandles = LCS.FnBindings $
                   LCF.insertHandleMap handle fnState curHandles in
  set (LCS.stateContext . LCS.functionBindings) newHandles state

-- | A 'AF.FunctionOverride' can contain references to:
--
-- * Auxiliary functions or forward declarations (see
--   @Note [Resolving forward declarations]@ in
--   "Ambient.FunctionOverride.Overrides.ForwardDeclarations"), all of which
--   have associated 'LCF.FnHandle's. This function inserts all of these handles
--   into a 'LCF.FnHandleMap'.
--
-- * Externs, which have associated 'LCS.GlobalVar's. This function inserts all
--   of these global variables into the 'LCSG.SymGlobalState'.
--
-- This function is monadic because constructing the overrides for forward
-- declarations can fail if the declared function name cannot be found.
-- (Similarly for externs.)
insertFunctionOverrideReferences ::
  forall sym bak arch scope solver st fs p ext args ret.
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , ext ~ DMS.MacawExt arch
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  AF.FunctionABI arch sym p ->
  AF.FunctionOverride p sym args arch ret ->
  LCF.FnHandleMap (LCS.FnState p sym ext) ->
  LCSG.SymGlobalState sym ->
  IO (LCF.FnHandleMap (LCS.FnState p sym ext), LCSG.SymGlobalState sym)
insertFunctionOverrideReferences bak abi = go
  where
    go :: forall args' ret'.
      AF.FunctionOverride p sym args' arch ret' ->
      LCF.FnHandleMap (LCS.FnState p sym ext) ->
      LCSG.SymGlobalState sym ->
      IO (LCF.FnHandleMap (LCS.FnState p sym ext), LCSG.SymGlobalState sym)
    go fnOverride handles0 globals0 = do
      -- First, insert any externs that are used in the override into the
      -- SymGlobalState...
      globals1 <-
        F.foldlM
          (\gbls (externName, Some externVar) -> do
            Some gblVar <-
              case Map.lookup externName (AF.functionGlobalMapping abi) of
                Just someGblVar -> pure someGblVar
                Nothing -> CMC.throwM $ AE.ExternNameNotFound externName
            WI.Refl <-
              case WI.testEquality (LCS.globalType externVar) (LCS.globalType gblVar) of
                Just eq -> pure eq
                Nothing -> CMC.throwM $ AE.ExternTypeMismatch externName
            case LCSG.lookupGlobal gblVar gbls of
              Just gblVal -> pure $ LCSG.insertGlobal externVar gblVal gbls
              Nothing ->
                AP.panic AP.SymbolicExecution
                        "insertFunctionOverrideReferences"
                        [ "Failed to find value for global variable: "
                          ++ DT.unpack (LCS.globalName gblVar)
                        ])
          globals0
          (Map.toAscList $ AF.functionExterns fnOverride)

      -- ...next, register any auxiliary functions that are used in the
      -- override...
      let handles1 =
            F.foldl' (\hdls (LCS.FnBinding fnHdl fnSt) ->
                       LCF.insertHandleMap fnHdl fnSt hdls)
                     handles0
                     (AF.functionAuxiliaryFnBindings fnOverride)

      -- ...and finally, register overrides for any forward declarations. In
      -- addition to registering the override for the forward declaration
      -- itself, we must also recursively register any forward declarations
      -- contained within the resolved function's override.
      F.foldlM
        (\hdlsAndGbls@(hdls, gbls) (fwdDecName, LCF.SomeHandle fwdDecHandle) ->
          do case LCF.lookupHandleMap fwdDecHandle hdls of
               Just _ ->
                 -- If the handle is already in the HandleMap, don't bother
                 -- reprocessing it. This isn't just an optimization—it's
                 -- important to ensure that this function terminates if it
                 -- invokes a function that uses mutually recursive forward
                 -- declarations.
                 pure hdlsAndGbls
               Nothing -> do
                 (ovSim, AF.SomeFunctionOverride resolvedFnOv) <-
                   AFOF.mkForwardDeclarationOverride
                     bak (AF.functionNameMapping abi) fwdDecName fwdDecHandle
                 let hdls' = LCF.insertHandleMap fwdDecHandle
                                                 (LCS.UseOverride ovSim)
                                                 hdls
                 go resolvedFnOv hdls' gbls)
        (handles1, globals1)
        (Map.toAscList $ AF.functionForwardDeclarations fnOverride)

-- Check if the supplied function address resides in one of the supplied
-- binaries. If so, return the resolved address offset and the index of the
-- binary that defines the address (see
-- @Note [Address offsets for shared libraries]@ in A.Loader.LoadOffset).
-- If it does not reside in one of the binaries, this function will panic.
resolveFuncAddrFromBinaries ::
  (w ~ DMC.ArchAddrWidth arch, DMM.MemWidth w) =>
  ALB.BinaryConfig arch binFmt ->
  DMM.MemWord w ->
  IO (DMM.MemSegmentOff w, Int)
resolveFuncAddrFromBinaries binConf =
  resolveFuncAddrFromMems $
  fmap (DMB.memoryImage . ALB.lbpBinary) (ALB.bcBinaries binConf)

-- Check if the supplied address resides in one of the supplied 'DMM.Memory'
-- values. If so, return the resolved address offset and the index of the
-- 'DMM.Memory' value in the 'NEV.NonEmptyVector' (see
-- @Note [Address offsets for shared libraries]@ in A.Loader.LoadOffset).
-- If it does not reside in one of these values, this function will panic.
resolveFuncAddrFromMems ::
  DMM.MemWidth w =>
  NEV.NonEmptyVector (DMM.Memory w) ->
  DMM.MemWord w ->
  IO (DMM.MemSegmentOff w, Int)
resolveFuncAddrFromMems mems funcAddr = do
  -- To determine which Memory to use, we need to compute the index for
  -- the appropriate binary. See Note [Address offsets for shared libraries]
  -- in A.Loader.LoadOffset.
  let memIndex = fromInteger $ ALL.addressToIndex funcAddr
  mem <- case mems NEV.!? memIndex of
    Just mem -> pure mem
    Nothing -> AP.panic AP.SymbolicExecution
                        "resolveFuncAddr"
                        [   "Requested address "
                         ++ show funcAddr
                         ++ " from binary with index "
                         ++ show memIndex
                         ++ " but binaries vector contains only "
                         ++ show (NEV.length mems)
                         ++ " binaries."
                        ]
  case DMBE.resolveAbsoluteAddress mem funcAddr of
    Nothing -> AP.panic AP.SymbolicExecution "resolveFuncAddrFromMems"
                 ["Failed to resolve function address: " ++ show funcAddr]
    Just funcAddrOff -> pure (funcAddrOff, memIndex)

-- | This function is used to generate a function handle for an override once a
-- syscall is encountered during symbolic execution.
symExLookupSyscall
  :: forall sym bak arch p ext scope solver st fs
   . ( WI.IsExpr (WI.SymExpr sym)
     , LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , DMS.SymArchConstraints arch
     , p ~ AExt.AmbientSimulatorState sym arch
     , ext ~ DMS.MacawExt arch
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     )
  => bak
  -> ASy.SyscallABI arch sym p
  -- ^ System call ABI specification for 'arch'
  -> LCF.HandleAllocator
  -> DMS.LookupSyscallHandle p sym arch
symExLookupSyscall bak abi hdlAlloc =
  DMS.LookupSyscallHandle $ \(atps :: LCT.CtxRepr atps) (rtps :: LCT.CtxRepr rtps) state0 reg -> do
    -- Extract system call number from register state
    syscallReg <- liftIO $ ASy.syscallNumberRegister abi bak atps reg
    let regVal = LCS.regValue syscallReg
    syscallNum <- resolveConcreteStackVal bak (Proxy @arch) AE.SyscallNumber regVal

    let syscallName = fromMaybe
          (AP.panic AP.SymbolicExecution "symExLookupSyscall"
            ["Unknown syscall with code " ++ show syscallNum])
            (IM.lookup (fromIntegral syscallNum) (ASy.syscallCodeMapping abi))

    -- Look for override associated with system call number, registering it if
    -- it has not already been so.
    (hndl, state1) <- lazilyRegisterHandle state0 atps rtps syscallNum syscallName

    pure (hndl, state1)
  where
    -- This function abstracts over a common pattern when dealing with lazily
    -- registering overrides (see Note [Lazily registering overrides] in
    -- A.Extensions):
    --
    -- First, check to see if the syscall has had an override registered
    -- previously by looking in the AmbientSimulatorState. (See
    -- Note [Lazily registering overrides] in A.Extensions.) If so, just use
    -- that handle. If not, apply a user-supplied override for this syscall.
    lazilyRegisterHandle :: forall atps rtps rtp blocks r ctx
                          . LCS.CrucibleState p sym ext rtp blocks r ctx
                         -> LCT.CtxRepr atps
                         -> LCT.CtxRepr rtps
                         -> Integer
                         -> DT.Text
                         -> IO ( LCF.FnHandle atps (LCT.StructType rtps)
                               , LCS.CrucibleState p sym ext rtp blocks r ctx
                               )
    lazilyRegisterHandle state atps rtps syscallNum syscallName = do
      let syscallNumRepr = ASy.SyscallNumRepr atps rtps syscallNum
      case MapF.lookup syscallNumRepr (state ^. LCS.stateContext . LCS.cruciblePersonality . AExt.syscallOvHandles) of
        Just (ASy.SyscallFnHandle handle) ->
          pure (handle, state)
        Nothing ->
          applyOverride state syscallNumRepr syscallName

    -- Apply a user-supplied override for the syscall, throwing an exception if
    -- an override cannot be found.
    applyOverride :: forall atps rtps rtp blocks r ctx
                   . LCS.CrucibleState p sym ext rtp blocks r ctx
                  -> ASy.SyscallNumRepr '(atps, rtps)
                  -> DT.Text
                  -> IO ( LCF.FnHandle atps (LCT.StructType rtps)
                        , LCS.CrucibleState p sym ext rtp blocks r ctx
                        )
    applyOverride state syscallNumRepr@(ASy.SyscallNumRepr atps rtps syscallNum) syscallName =
      case Map.lookup syscallName (ASy.syscallOverrideMapping abi) of
        Just (ASy.SomeSyscall syscall) -> do
          (handle, state') <- mkAndBindOverride state atps rtps syscall
          let state'' = over (LCS.stateContext . LCS.cruciblePersonality . AExt.syscallOvHandles)
                             (MapF.insert syscallNumRepr (ASy.SyscallFnHandle handle))
                             state'
          pure (handle, state'')
        Nothing -> do
          let sym = LCB.backendGetSym bak
          loc <- liftIO $ WI.getCurrentProgramLoc sym
          CMC.throwM $ AE.UnsupportedSyscallNumber loc syscallName syscallNum

    mkAndBindOverride :: forall atps rtps syscallArgs syscallRet rtp blocks r ctx
                       . LCS.CrucibleState p sym ext rtp blocks r ctx
                      -> LCT.CtxRepr atps
                      -> LCT.CtxRepr rtps
                      -> ASy.Syscall p sym syscallArgs ext syscallRet
                      -> IO ( LCF.FnHandle atps (LCT.StructType rtps)
                            , LCS.CrucibleState p sym ext rtp blocks r ctx
                            )
    mkAndBindOverride state atps rtps syscall = do
      -- Construct an override for the system call
      let retOV :: forall r'
                 . LCSO.OverrideSim p sym ext r' atps (LCT.StructType rtps)
                                    (Ctx.Assignment (LCS.RegValue' sym) rtps)
          retOV = do
            argMap <- LCSO.getOverrideArgs
            let argReg = massageRegAssignment $ LCS.regMap argMap
            args <- liftIO $
              ASy.syscallArgumentRegisters abi bak atps argReg
                                           (ASy.syscallArgTypes syscall)
            ASy.syscallReturnRegisters abi (ASy.syscallReturnType syscall)
                                           (ASy.syscallOverride syscall bak args)
                                           atps argReg rtps

      let ov :: LCSO.Override p sym ext atps (LCT.StructType rtps)
          ov = LCSO.mkOverride' (ASy.syscallName syscall)
                                (LCT.StructRepr rtps) retOV

      -- Build a function handle for the override and insert it into the
      -- state
      bindOverrideHandle state hdlAlloc atps rtps ov

    -- Massage the RegEntry Assignment that getOverrideArgs provides into the
    -- form that Syscall expects.
    massageRegAssignment ::
         Ctx.Assignment (LCS.RegEntry sym) ctx
      -> LCS.RegEntry sym (LCT.StructType ctx)
    massageRegAssignment assn =
      LCS.RegEntry (LCT.StructRepr (FC.fmapFC LCS.regType assn))
                   (FC.fmapFC (LCS.RV . LCS.regValue) assn)

-- | Resolve a bitvector value that was spilled to the stack as concrete. This
-- is used for both syscall numbers and function addresses, and it requires
-- some fancy footwork to do successfully.
-- See @Note [Resolving concrete syscall numbers and function addresses]@.
resolveConcreteStackVal ::
     ( LCB.IsSymInterface sym
     , DMS.SymArchConstraints arch
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     )
  => LCBO.OnlineBackend solver scope st fs
  -> proxy arch
  -> AE.ConcretizationTarget
  -> WI.SymBV sym (DMC.ArchAddrWidth arch)
  -> IO Integer
resolveConcreteStackVal bak _ target stackVal = do
  let sym = LCB.backendGetSym bak
  loc <- WI.getCurrentProgramLoc sym

  res <- AVC.resolveSymBVAs bak WT.knownNat stackVal
  case res of
    Left AVC.SolverUnknown ->
      CMC.throwM $ AE.ConcretizationFailedUnknown loc target
    Left AVC.UnsatInitialAssumptions ->
      AP.panic AP.SymbolicExecution "resolverConcreteStackVal"
        ["Initial assumptions are unsatisfiable at " ++ show (PP.pretty (WP.plSourceLoc loc))]
    Left AVC.MultipleModels ->
      CMC.throwM $ AE.ConcretizationFailedSymbolic loc target
    Right stackVal' ->
      pure $ BVS.asUnsigned stackVal'

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

globalMemoryHooks :: forall w
                   . ( DMM.MemWidth w )
                  => NEV.NonEmptyVector (DMM.Memory w)
                  -- ^ The memory for each loaded binary
                  -> Map.Map ALV.VersionedGlobalVarName (DMM.MemWord w)
                  -- ^ Mapping from shared library global variables to their
                  -- addresses
                  -> Map.Map (DMM.MemWord w) ALR.RelocType
                  -- ^ Supported relocation types
                  -> DMSM.GlobalMemoryHooks w
globalMemoryHooks allMems globals supportedRelocs = DMSM.GlobalMemoryHooks {
    DMSM.populateRelocation = \bak relocMem relocSeg relocBaseAddr reloc -> do
      -- This function populates relocation types we support as appropriate.
      -- It populates all other relocations with symbolic bytes.
      let sym = LCB.backendGetSym bak
      let relocAbsBaseAddr = memAddrToAbsAddr relocMem relocSeg relocBaseAddr
      case Map.lookup relocAbsBaseAddr supportedRelocs of
        Just relocType ->
          case relocType of
            ALR.RelativeReloc -> relativeRelocHook sym reloc relocAbsBaseAddr
            ALR.SymbolReloc   -> withSymbolRelocation sym reloc $ \name version ->
                                 symbolRelocHook sym name version reloc
            ALR.CopyReloc     -> withSymbolRelocation sym reloc $ \name version ->
                                 copyRelocHook bak name version reloc
        Nothing ->
          symbolicRelocation sym reloc Nothing
  }
  where
    -- Used for recursive calls to populateRelocation in copyRelocHook
    hooks = globalMemoryHooks allMems globals supportedRelocs

    -- Build a symbolic relocation value for 'reloc'.  We use this for
    -- relocation types we don't yet support.
    symbolicRelocation sym reloc mName = do
      let name = (fromMaybe "unknown" mName) ++ "-reloc"
      mapM (symbolicByte sym name) [1..(DMM.relocationSize reloc)]

    -- Construct a symbolic byte.
    symbolicByte sym name idx = do
      let symbol = WI.safeSymbol $ name ++ "-byte" ++ show (idx-1)
      WI.freshConstant sym symbol WI.knownRepr

    -- Convert a 'DMM.MemAddr' to an absolute address.
    memAddrToAbsAddr ::
         DMM.Memory w -> DMM.MemSegment w
      -> DMM.MemAddr w -> DMM.MemWord w
    memAddrToAbsAddr mem seg addr =
      case DMM.resolveRegionOff mem (DMM.addrBase addr) (DMM.addrOffset addr) of
        Just addrOff -> DMM.segmentOffset seg + DMM.segoffOffset addrOff
        Nothing -> AP.panic AP.SymbolicExecution "memAddrToAbsAddr"
                     ["Failed to resolve function address: " ++ show addr]

    -- If the supplied Relocation is a SymbolRelocation, invoke the
    -- continuation argument on its name and version. Otherwise, default to
    -- returning symbolic bytes.
    withSymbolRelocation ::
         forall sym
       . LCB.IsSymInterface sym
      => sym
      -> DMM.Relocation w
      -> (DMM.SymbolName -> DMM.SymbolVersion -> IO [WI.SymBV sym 8])
      -> IO [WI.SymBV sym 8]
    withSymbolRelocation sym reloc k =
      case DMM.relocationSym reloc of
        DMM.SymbolRelocation name version -> k name version
        _ -> symbolicRelocation sym reloc Nothing

    -- Compute the address that a relocation references and convert it to a
    -- list of bytes.
    relocAddrBV ::
         forall sym
       . LCB.IsSymInterface sym
      => sym
      -> DMM.Relocation w
      -> DMM.MemWord w
      -> IO [WI.SymBV sym 8]
    relocAddrBV sym reloc relocAbsBaseAddr = do
      -- First, compute the address by adding the offset...
      let relocAddr = relocAbsBaseAddr + DMM.relocationOffset reloc

      -- ...next, chunk up the address into bytes...
      let bv = BVS.mkBV (DMM.memWidthNatRepr @w) (fromIntegral relocAddr)
      let bytesLE = fromMaybe
            (AP.panic AP.SymbolicExecution
                      "relocAddrToSymbolicBytes"
                      ["Failed to split bitvector into bytes"])
            (BVS.asBytesLE (DMM.memWidthNatRepr @w) bv)

      --- ...finally, convert each byte to a SymBV.
      traverse (WI.bvLit sym (WI.knownNat @8) . BVS.word8) bytesLE

    -- Handle a symbol relocation. This involves copying the address of a
    -- global variable defined elsewhere. Discovering this address is a
    -- straightforward matter of looking it up in the supplied global variable
    -- Map.
    symbolRelocHook :: forall sym
                      . LCB.IsSymInterface sym
                    => sym
                    -> BS.ByteString
                    -> BinSym.SymbolVersion
                    -> DMM.Relocation w
                    -> IO [WI.SymBV sym 8]
    symbolRelocHook sym name version reloc =
      case Map.lookup (ALV.VerSym name version) globals of
        Just relocAbsBaseAddr -> relocAddrBV sym reloc relocAbsBaseAddr
        Nothing -> symbolicRelocation sym reloc (Just (show name))

    -- Handle a COPY relocation. This involves copying the value of a global
    -- variable defined in another shared library. See
    -- Note [Global symbols and COPY relocations] in
    -- Ambient.Loader.ELF.Symbols.
    --
    -- Discovering this value is a bit involved, as it requires:
    --
    -- 1. Looking up the address of the global variable that the relocation
    --    references, and
    --
    -- 2. Looking up the 'MemChunk' located at that address, which contains
    --    the value to copy.
    --
    -- 3. Finally, take an amount of bytes from the MemChunk equal in size
    --    to the number of bytes in the relocation region. This is important
    --    in case the region that the relocation references is larger in size.
    copyRelocHook :: forall sym bak
                   . LCB.IsSymBackend sym bak
                  => bak
                  -> BS.ByteString
                  -> BinSym.SymbolVersion
                  -> DMM.Relocation w
                  -> IO [WI.SymBV sym 8]
    copyRelocHook bak name version reloc =
      let sym = LCB.backendGetSym bak in
      -- Step (1)
      case Map.lookup (ALV.VerSym name version) globals of
        Just relocAddr -> do
          -- NB: COPY relocations always have a relocationOffset of 0, so there
          -- is no need to add it.
          (segOff, memIndex) <- resolveFuncAddrFromMems allMems relocAddr
          let mem = allMems NEV.! memIndex
          let segRelAddr = DMM.segoffAddr segOff
          -- Step (2)
          chunkBytes <- case DMM.segoffContentsAfter segOff of
            Left memErr -> CMC.throwM $ AE.RelocationMemoryError memErr
            Right chunks -> case chunks of
              [] -> CMC.throwM $ AE.RelocationMemoryError
                               $ DMM.AccessViolation segRelAddr

              -- TODO: Is it possible that a COPY relocation could point to the
              -- middle of a MemChunk? If that is the case, then we would need
              -- to grab bytes from subsequent MemChunks in order to have
              -- enough bytes to populate the entire size of the relocation.
              -- On the other hand, macaw is quite good about putting each
              -- global variable into its own MemChunk, so I'm unclear if this
              -- can ever happen in practice.

              -- It is possible that the target of a COPY relocation is itself
              -- a relocation. For example, stderr is defined in uClibc by way
              -- of an R_ARM_RELATIVE relocation, and other binaries will in
              -- turn reference stderr using R_ARM_COPY. As a result, we have
              -- to follow the relocations to get to the actual value to copy.
              DMM.RelocationRegion r : _ ->
                DMSM.populateRelocation hooks bak mem
                  (DMM.segoffSegment segOff)
                  (DMM.segoffAddr segOff)
                  r
              DMM.BSSRegion sz : _ ->
                replicate (fromIntegral sz) <$> WI.bvLit sym w8 (BVS.zero w8)
              DMM.ByteRegion bytes : _ ->
                traverse (WI.bvLit sym w8 . BVS.word8) $ BS.unpack bytes
          -- Step (3)
          pure $ take (DMM.relocationSize reloc) chunkBytes
        _ -> symbolicRelocation sym reloc (Just (show name))

    -- Handle a RELATIVE relocation. This is perhaps the simplest type of
    -- relocation to handle, as there are no symbol names to cross-reference.
    -- All we have to do is compute the address that the relocation references.
    relativeRelocHook :: forall sym
                       . LCB.IsSymInterface sym
                      => sym
                      -> DMM.Relocation w
                      -> DMM.MemWord w
                      -> IO [WI.SymBV sym 8]
    relativeRelocHook = relocAddrBV

    w8 = WI.knownNat @8

initializeMemory
  :: forall sym bak arch w p m t st fs
   . ( ?memOpts :: LCLM.MemOptions
     , MonadIO m
     , LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , KnownNat w
     , sym ~ WE.ExprBuilder t st fs
     , 1 <= w
     , 16 <= w )
  => bak
  -> LCF.HandleAllocator
  -> DMA.ArchitectureInfo arch
  -> NEV.NonEmptyVector (DMM.Memory w)
  -> AM.InitArchSpecificGlobals arch
  -- ^ Function to initialize special global variables needed for 'arch'
  -> AM.MemoryModel ()
  -- ^ Which memory model configuration to use
  -> [ AF.SomeFunctionOverride p sym arch ]
  -- ^ A list of additional function overrides to register.
  -> Map.Map ALV.VersionedGlobalVarName (DMM.MemWord w)
  -- ^ Mapping from shared library global variables to their addresses
  -> Map.Map (DMM.MemWord w) ALR.RelocType
  -- ^ Supported relocation types
  -> m ( AM.InitialMemory sym w )
initializeMemory bak halloc archInfo mems (AM.InitArchSpecificGlobals initGlobals)
                 memModel functionOvs globals supportedRelocs = do
  let sym = LCB.backendGetSym bak

  -- Initialize memory
  let endianness = DMSM.toCrucibleEndian (DMA.archEndianness archInfo)
  (initMem, memPtrTbl) <-
    AEM.newMemPtrTable (globalMemoryHooks mems globals supportedRelocs) bak endianness mems
  let validityCheck = AEM.mkGlobalPointerValidityPred memPtrTbl
  let globalMap = AEM.mapRegionPointers memPtrTbl

  -- Allocate memory for the stack, initialize it with symbolic contents, and
  -- then insert it into the memory model
  stackArrayStorage <- liftIO $ WI.freshConstant sym (WSym.safeSymbol "stack_array") WI.knownRepr
  stackSizeBV <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackSize)
  let ?ptrWidth = WI.knownRepr
  (stackBasePtr, mem1) <- liftIO $ LCLM.doMalloc bak LCLM.StackAlloc LCLM.Mutable "stack_alloc" initMem stackSizeBV LCLD.noAlignment
  mem2 <- liftIO $ LCLM.doArrayStore bak mem1 stackBasePtr LCLD.noAlignment stackArrayStorage stackSizeBV
  (mem3, globals0) <- liftIO $ initGlobals bak mem2
  memVar <- liftIO $ LCLM.mkMemVar (DT.pack "ambient-verifier::memory") halloc

  (memModel', globals1) <-
    case memModel of
      AM.DefaultMemoryModel ->
        let globals1 = LCSG.insertGlobal memVar mem3 globals0 in
        pure (AM.DefaultMemoryModel, globals1)
      AM.BumpAllocator () -> do
        -- Initialize heap memory for bump allocator
        heapSizeBv <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr heapSize)
        (heapBasePtr, mem4) <- liftIO $ LCLM.doMalloc bak LCLM.HeapAlloc LCLM.Mutable "<malloc bump>" mem3 heapSizeBv LCLD.noAlignment
        heapEndPtr <- liftIO $ LCLM.ptrAdd sym WI.knownRepr heapBasePtr heapSizeBv
        heapEndGlob <- liftIO $ LCCC.freshGlobalVar halloc
                                                    (DT.pack "heapFreeEnd")
                                                    (LCLM.LLVMPointerRepr WI.knownNat)
        let globals1 = LCSG.insertGlobal memVar mem4 $
                       LCSG.insertGlobal heapEndGlob heapEndPtr globals0
        pure (AM.BumpAllocator heapEndGlob, globals1)

  let functionOvGlobals = Map.unions [ AF.functionGlobals ov
                                     | AF.SomeFunctionOverride ov <- functionOvs ]
  globals2 <- liftIO $ insertFreshGlobals sym functionOvGlobals globals1

  return (AM.InitialMemory { AM.imMemModel = memModel'
                           , AM.imMemVar = memVar
                           , AM.imGlobals = globals2
                           , AM.imStackBasePtr = stackBasePtr
                           , AM.imValidityCheck = validityCheck
                           , AM.imGlobalMap = globalMap
                           , AM.imMemPtrTable = memPtrTbl
                           })

-- | The values of the arguments to the @main()@ function.
--
-- See @Note [Simulating main()]@ in @Options@.
data MainArgVals sym w = MainArgVals
  { argcVal :: WI.SymBV sym w
  , argvVal :: LCLM.LLVMPtr sym w
  , envpVal :: LCLM.LLVMPtr sym w
  }

-- | Populate the registers corresponding to @main(...)@'s arguments with the
-- user-supplied command line arguments.
--
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

-- | Configuration parameters concerning functions and overrides
data FunctionConfig arch sym p = FunctionConfig {
    fcBuildSyscallABI :: ASy.BuildSyscallABI arch sym p
  -- ^ Function to construct an ABI specification for system calls
  , fcBuildFunctionABI :: AF.BuildFunctionABI arch sym p
  -- ^ Function to construct an ABI specification for function calls
  , fcCrucibleSyntaxOverrides :: AFET.CrucibleSyntaxOverrides (DMC.ArchAddrWidth arch) p sym arch
  -- ^ @crucible-syntax@ overrides to register
  }

simulateFunction
  :: ( CMC.MonadThrow m
     , MonadIO m
     , ext ~ DMS.MacawExt arch
     , LCCE.IsSyntaxExtension ext
     , LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , DMB.BinaryLoader arch binFmt
     , DMS.SymArchConstraints arch
     , w ~ DMC.ArchAddrWidth arch
     , 16 <= w
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , ?memOpts :: LCLM.MemOptions
     , p ~ AExt.AmbientSimulatorState sym arch
     )
  => LJ.LogAction IO AD.Diagnostic
  -> bak
  -> [LCS.GenericExecutionFeature sym]
  -> LCF.HandleAllocator
  -> DMA.ArchitectureInfo arch
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -> SymbolicExecutionConfig arch sym
  -> AM.InitialMemory sym w
  -> DMC.ArchSegmentOff arch
  -- ^ The address of the entry point function
  -> Maybe FilePath
  -- ^ Path to the symbolic filesystem.  If this is 'Nothing', the file system
  -- will be empty
  -> Maybe FilePath
  -- ^ Optional path to the file to log function calls to
  -> ALB.BinaryConfig arch binFmt
  -- ^ Information about the loaded binaries
  -> FunctionConfig arch sym p
  -- ^ Configuration parameters concerning functions and overrides
  -> [BS.ByteString]
  -- ^ The user-supplied command-line arguments
  -> Map.Map BS.ByteString [WI.SymBV sym 8]
  -- ^ The user-supplied environment variables
  -> m (SymbolicExecutionResult arch sym)
simulateFunction logAction bak execFeatures halloc archInfo archVals seConf initialMem entryPointAddr mFsRoot mFnCallLog binConf fnConf cliArgs envVars = do
  let sym = LCB.backendGetSym bak
  let symArchFns = DMS.archFunctions archVals
  let crucRegTypes = DMS.crucArchRegTypes symArchFns
  let regsRepr = LCT.StructRepr crucRegTypes

  -- Set up an initial register state (mostly symbolic, with an initial stack)
  --
  -- Put the stack pointer in the middle of our allocated stack so that both sides can be addressed
  initialRegs <- liftIO $ DMS.macawAssignToCrucM (mkInitialRegVal symArchFns sym) (DMS.crucGenRegAssignment symArchFns)
  stackInitialOffset <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackOffset)
  sp <- liftIO $ LCLM.ptrAdd sym WI.knownRepr (AM.imStackBasePtr initialMem) stackInitialOffset
  let initialRegsEntry = LCS.RegEntry regsRepr initialRegs
  let regsWithStack = DMS.updateReg archVals initialRegsEntry DMC.sp_reg sp

  -- Initialize the file system
  fileContents <- liftIO $
    case mFsRoot of
      Nothing -> return LCSy.emptyInitialFileSystemContents
      Just fsRoot -> LCSL.loadInitialFiles sym fsRoot
  let ?ptrWidth = WI.knownRepr
  (fs, globals0, LCLS.SomeOverrideSim initFSOverride) <- liftIO $
    LCLS.initialLLVMFileSystem halloc sym WI.knownRepr fileContents [] (AM.imGlobals initialMem)

  environGlob <- liftIO $
    LCCC.freshGlobalVar halloc
                        (DT.pack "AMBIENT_environ")
                        LCLM.PtrRepr

  let csOverrides = fcCrucibleSyntaxOverrides fnConf
  let ASy.BuildSyscallABI buildSyscallABI = fcBuildSyscallABI fnConf
  let syscallABI = buildSyscallABI fs initialMem (ALB.bcUnsuportedRelocations binConf)
  let AF.BuildFunctionABI buildFunctionABI = fcBuildFunctionABI fnConf
  let functionABI = buildFunctionABI AF.TestContext fs initialMem archVals
                                     (ALB.bcUnsuportedRelocations binConf)
                                     (AFET.csoAddressOverrides csOverrides)
                                     (AFET.csoNamedOverrides csOverrides)
                                     [Some environGlob]

  let mem0 = case LCSG.lookupGlobal (AM.imMemVar initialMem) globals0 of
               Just mem -> mem
               Nothing  -> AP.panic AP.FunctionOverride "simulateFunction"
                             [ "Failed to find global variable for memory: "
                               ++ show (LCCC.globalName (AM.imMemVar initialMem)) ]
  (mainReg0, mainReg1, mainReg2) <-
    case AF.functionIntegerArgumentRegisters functionABI of
      (reg0:reg1:reg2:_) -> pure (reg0, reg1, reg2)
      _ -> AP.panic AP.SymbolicExecution "simulateFunction"
             [ "Not enough registers for the main() function" ]
  (mainArgVals, regsWithMainArgs, mem1) <- liftIO $
    initMainArguments bak mem0 archVals mainReg0 mainReg1 mainReg2 cliArgs envVars regsWithStack
  let globals2 = LCSG.insertGlobal (AM.imMemVar initialMem) mem1 $
                 LCSG.insertGlobal environGlob (envpVal mainArgVals) globals0
  let arguments = LCS.RegMap (Ctx.singleton regsWithMainArgs)

  let mainBinaryPath = ALB.mainLoadedBinaryPath binConf
  Some discoveredEntry <- ADi.discoverFunction logAction archInfo mainBinaryPath entryPointAddr
  LCCC.SomeCFG cfg <- ALi.liftDiscoveredFunction halloc (ALB.lbpPath mainBinaryPath)
                                                 (DMS.archFunctions archVals) discoveredEntry
  let simAction = LCS.runOverrideSim regsRepr $ do
                    -- First, initialize the symbolic file system...
                    initFSOverride
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
                                (AFET.csoStartupOverrides csOverrides)
                    -- ...and finally, run the entrypoint function.
                    LCS.regValue <$> LCS.callCFG cfg arguments

  DMS.withArchEval archVals sym $ \archEvalFn -> do
    let extImpl = AExt.ambientExtensions bak archEvalFn initialMem (symExLookupFunction logAction bak initialMem archVals binConf functionABI halloc archInfo mFnCallLog) (symExLookupSyscall bak syscallABI halloc) (ALB.bcUnsuportedRelocations binConf)
    -- Register any externs, auxiliary functions, forward declarations used in
    -- the startup overrides.
    (startupBindings, globals4) <-
      F.foldlM (\(bindings, globals) functionOv ->
                 liftIO $ insertFunctionOverrideReferences
                            bak functionABI functionOv bindings globals)
               (LCF.emptyHandleMap, globals2)
               (AFET.csoStartupOverrides csOverrides)
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
    let ctx = LCS.initSimContext bak (MapF.union LCLI.llvmIntrinsicTypes LCLS.llvmSymIOIntrinsicTypes) halloc IO.stdout (LCS.FnBindings bindings) extImpl ambientSimState
    let s0 = LCS.InitialState ctx globals4 LCS.defaultAbortHandler regsRepr simAction
    let sbsRecorder = sbsFeature logAction
    let executionFeatures = [sbsRecorder | secLogBranches seConf] ++ fmap LCS.genericToExecutionFeature execFeatures

    res <- liftIO $ LCS.executeCrucible executionFeatures s0
    return $ SymbolicExecutionResult (AM.imMemVar initialMem)
                                     res
  where
    -- Syntax overrides cannot make use of variadic arguments, so if this
    -- callback is ever used, something has gone awry.
    dummyGetVarArg :: AF.GetVarArg sym
    dummyGetVarArg = AF.GetVarArg $ \_ ->
      AP.panic AP.SymbolicExecution "simulateFunction"
        ["A startup override cannot use variadic arguments"]

-- | Symbolically execute a function
--
-- Note that this function currently discards the results of symbolic execution
--
-- NOTE: This currently fixes the memory model as 'DMS.LLVMMemory' (i.e., the
-- default memory model for machine code); we will almost certainly need a
-- modified memory model.
symbolicallyExecute
  :: forall m sym bak arch binFmt w solver scope st fs ext p
   . ( CMC.MonadThrow m
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
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , ?memOpts :: LCLM.MemOptions
     , p ~ AExt.AmbientSimulatorState sym arch
     , LCLM.HasLLVMAnn sym
     )
  => LJ.LogAction IO AD.Diagnostic
  -> bak
  -> LCF.HandleAllocator
  -> DMA.ArchitectureInfo arch
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -> SymbolicExecutionConfig arch sym
  -> [LCS.GenericExecutionFeature sym]
  -> DMC.ArchSegmentOff arch
  -- ^ The address of the entry point function
  -> AM.MemoryModel ()
  -- ^ Which memory model configuration to use
  -> AM.InitArchSpecificGlobals arch
  -- ^ Function to initialize special global variables needed for 'arch'
  -> Maybe FilePath
  -- ^ Path to the symbolic filesystem.  If this is 'Nothing', the file system
  -- will be empty
  -> Maybe FilePath
  -- ^ Optional path to the file to log function calls to
  -> ALB.BinaryConfig arch binFmt
  -- ^ Information about the loaded binaries
  -> FunctionConfig arch sym p
  -- ^ Configuration parameters concerning functions and overrides
  -> [BS.ByteString]
  -- ^ The user-supplied command-line arguments
  -> Map.Map BS.ByteString [WI.SymBV sym 8]
  -- ^ The user-supplied environment variables
  -> m (SymbolicExecutionResult arch sym)
symbolicallyExecute logAction bak halloc archInfo archVals seConf execFeatures entryPointAddr memModel initGlobals mFsRoot mFnCallLog binConf fnConf cliArgs envVars = do
  let mems = fmap (DMB.memoryImage . ALB.lbpBinary) (ALB.bcBinaries binConf)
  initialMem <- initializeMemory bak
                                 halloc
                                 archInfo
                                 mems
                                 initGlobals
                                 memModel
                                 (AFET.csoNamedOverrides (fcCrucibleSyntaxOverrides fnConf))
                                 (ALB.bcDynamicGlobalVarAddrs binConf)
                                 (ALB.bcSupportedRelocations binConf)
  simulateFunction logAction bak execFeatures halloc archInfo archVals seConf initialMem entryPointAddr mFsRoot mFnCallLog binConf fnConf cliArgs envVars
