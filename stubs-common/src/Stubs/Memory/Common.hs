{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}

-- | Memory definitions useful in several architectures
module Stubs.Memory.Common where 
  
import qualified Lang.Crucible.Simulator as LCS
import qualified Data.Parameterized.Ctx as Ctx
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.Types as LCT
import qualified Data.Parameterized.TraversableFC as FC
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Stubs.Panic as AP
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Expr as LCCE
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.Symbolic as DMS
import qualified What4.Expr as WE
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Stubs.Extensions as AExt
import qualified Stubs.Memory as SM
import qualified Stubs.Loader.BinaryConfig as ALB
import qualified Stubs.FunctionOverride as AF
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Lumberjack as LJ
import qualified Stubs.Diagnostic as AD
import qualified What4.Protocol.Online as WPO
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Stubs.Discovery as SDi
import Data.Parameterized (Some(..))
import qualified Stubs.Lift as SLi
import Control.Lens (Lens', (^.), over, (.~), (&), set)
import qualified Data.Map as Map
import qualified Data.List.NonEmpty as NEL
import qualified Data.Vector.NonEmpty as NEV
import qualified Stubs.Loader.Versioning as SLV
import qualified Stubs.Exception as SE
import qualified Control.Monad.Catch as CMC
import qualified System.FilePath as SF
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Simulator.OverrideSim as LCSO
import qualified What4.Interface as WI
import qualified Stubs.Syscall as SSy
import qualified Data.IntMap as IM
import qualified Data.Parameterized.Map as MapF
import qualified Data.Text as DT
import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.Data (Proxy(..))
import Data.Maybe
import qualified What4.BaseTypes as WT
import qualified Prettyprinter as PP
import qualified What4.ProgramLoc as WP
import qualified Stubs.Verifier.Concretize as SVC
import qualified Data.BitVector.Sized as BVS
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LCLMP
import qualified Data.Macaw.BinaryLoader.ELF as DMBE
import qualified Stubs.Loader.LoadOptions as SLL
import qualified Data.Foldable as F
import qualified Data.Macaw.Symbolic.Memory as DMSM
import qualified Data.BinarySymbols as BinSym
import qualified Data.ByteString as BS
import qualified Stubs.Loader.Relocations as SLR


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
     , SM.IsStubsMemoryModel mem arch
     )
   => LJ.LogAction IO AD.Diagnostic
   -> bak
   -> SM.InitialMemory sym mem arch 
   -> DMS.GenArchVals mem arch
   -> ALB.BinaryConfig arch binFmt
   -- ^ Information about the loaded binaries
   -> SM.FunctionABI arch sym p mem
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
      Some discoveredEntry <- SDi.discoverFunction logAction archInfo bin funcAddrOff
      SLi.liftDiscoveredFunction hdlAlloc (ALB.lbpPath bin)
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
     , SM.IsStubsMemoryModel mem arch
     )
   => (DMM.MemSegmentOff w -> ALB.LoadedBinaryPath arch binFmt -> IO (LCCC.SomeCFG ext args ret))
   -- ^ How to construct a CFG for a function (given its address offset and
   -- binary) in the event that an override for the function cannot be found.
   -> LJ.LogAction IO AD.Diagnostic
   -> bak
   -> SM.InitialMemory sym mem arch
   -> DMS.GenArchVals mem arch
   -> ALB.BinaryConfig arch binFmt
   -- ^ Information about the loaded binaries
   -> SM.FunctionABI arch sym p mem
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
      then let mem = readGlobal (SM.imMemVar initialMem) state1 in
           SM.functionReturnAddr abi bak archVals regs mem
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
                           (SM.functionAddrMapping abi) $
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
                                 (SLV.versymSymbol pltStubVersym)
                                 AExt.functionOvHandles
                                 (SM.functionNameMapping abi) $ do
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
      SLV.VersionedFunctionName ->
      IO (DMM.MemSegmentOff w, ALB.LoadedBinaryPath arch binFmt)
    resolvePLTStub pltStubVersym =
      case Map.lookup pltStubVersym (ALB.bcDynamicFuncSymbolMap binConf) of
        Just funcAddr -> resolveFuncAddrAndBin funcAddr
        Nothing -> CMC.throwM (SE.UnhandledPLTStub pltStubVersym)

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
                           (SM.functionAddrMapping abi) $
      -- Step (4)
      case Map.lookup funcAddrOff (ALB.lbpEntryPoints bin) of
        Just fnVersyms ->
          -- Look up each of the symbol names associated with each address.
          -- If we find a handle for one of the names, stop searching and
          -- return that handle. Otherwise, fall back on 'lookupOrDiscoverFuncAddrOff'.
          let findHandleForSym fnSym findNextSym =
                lazilyRegisterHandle state fnSym
                                     AExt.functionOvHandles
                                     (SM.functionNameMapping abi)
                                     findNextSym in
          let fallback = lookupOrDiscoverFuncAddrOff funcAddrOff bin state in
          -- NB: When looking up overrides, we only consult the function name
          -- and completely ignore the version. In the future, we will want
          -- to allow users to specify overrides that only apply to
          -- particular versions. See #104.
          foldr findHandleForSym fallback (fmap SLV.versymSymbol fnVersyms)
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
            mem <- LCS.readGlobal $ SM.imMemVar initialMem
            argMap <- LCS.getOverrideArgs
            let argReg = massageRegAssignment $ LCS.regMap argMap
            (args, getVarArg) <- liftIO $
              SM.functionIntegerArguments abi bak
                                          (AF.functionArgTypes fnOverride)
                                          argReg mem
            retVal <- AF.functionOverride fnOverride bak args getVarArg parents
            SM.functionIntegerReturnRegisters abi bak archVals
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
  -> SM.SyscallABI arch sym p
  -- ^ System call ABI specification for 'arch'
  -> LCF.HandleAllocator
  -> DMS.LookupSyscallHandle p sym arch
symExLookupSyscall bak abi hdlAlloc =
  DMS.LookupSyscallHandle $ \(atps :: LCT.CtxRepr atps) (rtps :: LCT.CtxRepr rtps) state0 reg -> do
    -- Extract system call number from register state
    syscallReg <- liftIO $ SM.syscallNumberRegister abi bak atps reg
    let regVal = LCS.regValue syscallReg
    syscallNum <- resolveConcreteStackVal bak (Proxy @arch) SE.SyscallNumber regVal

    let syscallName = fromMaybe
          (AP.panic AP.SymbolicExecution "symExLookupSyscall"
            ["Unknown syscall with code " ++ show syscallNum])
            (IM.lookup (fromIntegral syscallNum) (SM.syscallCodeMapping abi))

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
      let syscallNumRepr = SSy.SyscallNumRepr atps rtps syscallNum
      case MapF.lookup syscallNumRepr (state ^. LCS.stateContext . LCS.cruciblePersonality . AExt.syscallOvHandles) of
        Just (SSy.SyscallFnHandle handle) ->
          pure (handle, state)
        Nothing ->
          applyOverride state syscallNumRepr syscallName

    -- Apply a user-supplied override for the syscall, throwing an exception if
    -- an override cannot be found.
    applyOverride :: forall atps rtps rtp blocks r ctx
                   . LCS.CrucibleState p sym ext rtp blocks r ctx
                  -> SSy.SyscallNumRepr '(atps, rtps)
                  -> DT.Text
                  -> IO ( LCF.FnHandle atps (LCT.StructType rtps)
                        , LCS.CrucibleState p sym ext rtp blocks r ctx
                        )
    applyOverride state syscallNumRepr@(SSy.SyscallNumRepr atps rtps syscallNum) syscallName =
      case Map.lookup syscallName (SM.syscallOverrideMapping abi) of
        Just (SSy.SomeSyscall syscall) -> do
          (handle, state') <- mkAndBindOverride state atps rtps syscall
          let state'' = over (LCS.stateContext . LCS.cruciblePersonality . AExt.syscallOvHandles)
                             (MapF.insert syscallNumRepr (SSy.SyscallFnHandle handle))
                             state'
          pure (handle, state'')
        Nothing -> do
          let sym = LCB.backendGetSym bak
          loc <- liftIO $ WI.getCurrentProgramLoc sym
          CMC.throwM $ SE.UnsupportedSyscallNumber loc syscallName syscallNum

    mkAndBindOverride :: forall atps rtps syscallArgs syscallRet rtp blocks r ctx
                       . LCS.CrucibleState p sym ext rtp blocks r ctx
                      -> LCT.CtxRepr atps
                      -> LCT.CtxRepr rtps
                      -> SSy.Syscall p sym syscallArgs ext syscallRet
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
              SM.syscallArgumentRegisters abi bak atps argReg
                                           (SSy.syscallArgTypes syscall)
            SM.syscallReturnRegisters abi (SSy.syscallReturnType syscall)
                                           (SSy.syscallOverride syscall bak args)
                                           atps argReg rtps

      let ov :: LCSO.Override p sym ext atps (LCT.StructType rtps)
          ov = LCSO.mkOverride' (SSy.syscallName syscall)
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
  -> SE.ConcretizationTarget
  -> WI.SymBV sym (DMC.ArchAddrWidth arch)
  -> IO Integer
resolveConcreteStackVal bak _ target stackVal = do
  let sym = LCB.backendGetSym bak
  loc <- WI.getCurrentProgramLoc sym

  res <- SVC.resolveSymBVAs bak WT.knownNat stackVal
  case res of
    Left SVC.SolverUnknown ->
      CMC.throwM $ SE.ConcretizationFailedUnknown loc target
    Left SVC.UnsatInitialAssumptions ->
      AP.panic AP.SymbolicExecution "resolverConcreteStackVal"
        ["Initial assumptions are unsatisfiable at " ++ show (PP.pretty (WP.plSourceLoc loc))]
    Left SVC.MultipleModels ->
      CMC.throwM $ SE.ConcretizationFailedSymbolic loc target
    Right stackVal' ->
      pure $ BVS.asUnsigned stackVal'

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
  resolveConcreteStackVal bak (Proxy @arch) SE.FunctionAddress offset
  where
    symArchFns :: DMS.MacawSymbolicArchFunctions arch
    symArchFns = DMS.archFunctions archVals

    crucRegTypes :: Ctx.Assignment LCT.TypeRepr (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
    crucRegTypes = DMS.crucArchRegTypes symArchFns

    regsRepr :: LCT.TypeRepr (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
    regsRepr = LCT.StructRepr crucRegTypes

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
  let memIndex = fromInteger $ SLL.addressToIndex funcAddr
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
  forall sym bak arch scope solver st fs p ext args ret mem.
  ( LCB.IsSymBackend sym bak
  , ext ~ DMS.MacawExt arch
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  SM.FunctionABI arch sym p mem->
  AF.FunctionOverride p sym args arch ret ->
  LCF.FnHandleMap (LCS.FnState p sym ext) ->
  LCSG.SymGlobalState sym ->
  IO (LCF.FnHandleMap (LCS.FnState p sym ext), LCSG.SymGlobalState sym)
insertFunctionOverrideReferences _ abi = go
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
              case Map.lookup externName (SM.functionGlobalMapping abi) of
                Just someGblVar -> pure someGblVar
                Nothing -> CMC.throwM $ SE.ExternNameNotFound externName
            WI.Refl <-
              case WI.testEquality (LCS.globalType externVar) (LCS.globalType gblVar) of
                Just eq -> pure eq
                Nothing -> CMC.throwM $ SE.ExternTypeMismatch externName
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
      return (handles1, globals1)

globalMemoryHooks :: forall w
                   . ( DMM.MemWidth w )
                  => NEV.NonEmptyVector (DMM.Memory w)
                  -- ^ The memory for each loaded binary
                  -> Map.Map SLV.VersionedGlobalVarName (DMM.MemWord w)
                  -- ^ Mapping from shared library global variables to their
                  -- addresses
                  -> Map.Map (DMM.MemWord w) SLR.RelocType
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
            SLR.RelativeReloc -> relativeRelocHook sym reloc relocAbsBaseAddr
            SLR.SymbolReloc   -> withSymbolRelocation sym reloc $ \name version ->
                                 symbolRelocHook sym name version reloc
            SLR.CopyReloc     -> withSymbolRelocation sym reloc $ \name version ->
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
      case Map.lookup (SLV.VerSym name version) globals of
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
      case Map.lookup (SLV.VerSym name version) globals of
        Just relocAddr -> do
          -- NB: COPY relocations always have a relocationOffset of 0, so there
          -- is no need to add it.
          (segOff, memIndex) <- resolveFuncAddrFromMems allMems relocAddr
          let mem = allMems NEV.! memIndex
          let segRelAddr = DMM.segoffAddr segOff
          -- Step (2)
          chunkBytes <- case DMM.segoffContentsAfter segOff of
            Left memErr -> CMC.throwM $ SE.RelocationMemoryError memErr
            Right chunks -> case chunks of
              [] -> CMC.throwM $ SE.RelocationMemoryError
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
