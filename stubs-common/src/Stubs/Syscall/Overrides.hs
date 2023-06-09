{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Defines syscall overrides that are shared across different architectures.
module Stubs.Syscall.Overrides
  ( allOverrides
  , buildExecveOverride
  , callExecve
  , buildNoOpMkdirOverride
  , exitOverride
  , callExit
  , getppidOverride
  , callGetppid
  , buildShmgetOverride
  , callShmget
  , shmatOverride
  , callShmat
    -- * Networking-related overrides
  , module Stubs.Syscall.Overrides.Networking
    -- * Symbolic IO–related overrides
  , module Stubs.Syscall.Overrides.SymIO
  ) where

import           Control.Lens ( (.=), (+=), use )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.CFG as DMC
import           Data.Macaw.X86.Symbolic ()
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.SimError as LCSS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Exception as AE
import           Stubs.Override
import qualified Stubs.Extensions as AExt
import qualified Stubs.Memory as AM
import qualified Stubs.Memory.SharedMemory as AMS
import           Stubs.Syscall
import           Stubs.Syscall.Overrides.Networking
import           Stubs.Syscall.Overrides.SymIO
import qualified Stubs.Verifier.Concretize as AVC

-- | All of the syscall overrides that work across all supported configurations.
allOverrides ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  ) =>
  LCLS.LLVMFileSystem w ->
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  Map.Map (DMC.MemWord w) String ->
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  [SomeSyscall (AExt.AmbientSimulatorState sym arch) sym ext]
allOverrides fs initialMem unsupportedRelocs = concat
  [ [ SomeSyscall buildExecveOverride
    , SomeSyscall exitOverride
    , SomeSyscall getppidOverride
    , SomeSyscall (buildShmgetOverride memVar)
    , SomeSyscall shmatOverride
      -- FIXME: This no-op override is for tracking purposes
      -- only.  It should be replaced with a more faithful
      -- override at some point.
    , SomeSyscall buildNoOpMkdirOverride
    ]
    -- Networking
  , networkOverrides fs initialMem unsupportedRelocs
    -- Symbolic IO
  , symIOOverrides fs initialMem unsupportedRelocs
  ]
  where
    memVar = AM.imMemVar initialMem

-- | Override for the 'execve' system call.  Currently this override records
-- that it was invoked through the 'hitExec' global, then aborts.
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- 'execve' arguments.
callExecve :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              )
           => bak
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callExecve bak = do
  let sym = LCB.backendGetSym bak
  loc <- liftIO $ WI.getCurrentProgramLoc sym
  liftIO $ LCB.abortExecBecause $ LCB.EarlyExit loc

buildExecveOverride :: LCLM.HasPtrWidth w
                    => Syscall p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType w)
buildExecveOverride =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "execve" $ \bak _args -> callExecve bak

-- | Override for the 'exit' system call.
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- 'exit' argument.
callExit :: ( LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            )
         => bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ Exit code
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym LCT.UnitType)
callExit bak reg = liftIO $
  do let sym = LCB.backendGetSym bak
     ec <- LCLM.projectLLVM_bv bak (LCS.regValue reg)
     cond <- WI.bvEq sym ec =<< WI.bvLit sym ?ptrWidth (BVS.zero ?ptrWidth)
     -- If the argument is non-zero, throw an assertion failure. Otherwise,
     -- simply stop the current thread of execution.
     -- NOTE: In the future we may not want to distinguish between zero and
     -- non-zero exit codes.
     LCB.assert bak cond (LCSS.AssertFailureSimError
                          "Call to exit() with non-zero argument"
                          "")
     loc <- WI.getCurrentProgramLoc sym
     LCB.abortExecBecause $ LCB.EarlyExit loc

exitOverride :: forall p sym ext w
              . LCLM.HasPtrWidth w
             => Syscall p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext (LCT.UnitType)
exitOverride =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "exit" $ \bak args ->
    Ctx.uncurryAssignment (callExit bak) args

-- | Override for the getppid(2) system call
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- 'getppid' return value.
callGetppid :: ( LCB.IsSymBackend sym bak
               , LCLM.HasPtrWidth w
               )
            => bak
            -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callGetppid bak = liftIO $ do
  let sym = LCB.backendGetSym bak
  -- The parent PID can change at any time due to reparenting, so this override
  -- always returns a new fresh value.
  symbolicResult <- WI.freshConstant sym
                                     (WI.safeSymbol "getppid")
                                     (WI.BaseBVRepr ?ptrWidth)
  LCLM.llvmPointer_bv sym symbolicResult

getppidOverride :: LCLM.HasPtrWidth w
                => Syscall p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType w)
getppidOverride =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "getppid" $ \bak _args -> callGetppid bak

-- | A no-op override for the mkdir(2) system call.  This override ignores any
-- arguments and always returns 0 for success.  It is intended to be used only
-- to track invocations of mkdir syscalls.
callNoOpMkdir :: ( LCB.IsSymBackend sym bak
                 , LCLM.HasPtrWidth w )
              => bak
              -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callNoOpMkdir bak = do
  let sym = LCB.backendGetSym bak
  zeroBv <- liftIO $ WI.bvLit sym ?ptrWidth (BVS.zero ?ptrWidth)
  liftIO $ bvToPtr sym zeroBv ?ptrWidth

buildNoOpMkdirOverride :: LCLM.HasPtrWidth w
                    => Syscall p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType w)
buildNoOpMkdirOverride =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "mkdir" $ \bak _args -> callNoOpMkdir bak

-- | Override for the @shmat(2)@ syscall.  This override only supports calls
-- where @shmaddr@ is @NULL@.  That is, it doesn't support calls where the
-- caller specifies which address the shared memory segment should be mapped
-- to.  This override also ignores the @shmflg@ argument and always maps the
-- memory as read/write.
callShmat :: forall sym scope st fs w solver arch m p ext r args ret
           . ( sym ~ WE.ExprBuilder scope st fs
             , LCB.IsSymInterface sym
             , LCLM.HasPtrWidth w
             , LCLM.HasLLVMAnn sym
             , WPO.OnlineSolver solver
             , p ~ AExt.AmbientSimulatorState sym arch
             , w ~ DMC.ArchAddrWidth arch
             , m ~ LCS.OverrideSim p sym ext r args ret
             )
          => LCBO.OnlineBackend solver scope st fs
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -> m (LCS.RegValue sym (LCLM.LLVMPointerType w))
callShmat bak shmid shmaddr _shmflg = do
  let sym = LCB.backendGetSym bak

  -- Check that shmaddr is NULL.
  nullCond <- liftIO $ LCLM.ptrIsNull sym ?ptrWidth (LCS.regValue shmaddr)
  liftIO $ LCB.assert bak nullCond (LCS.AssertFailureSimError
                                   "Call to shmat() with non-null shmaddr"
                                   "")

  -- Extract ID and lookup in shared memory state
  (shmIdSymBv, resolveEffect) <- liftIO $
        LCLM.projectLLVM_bv bak (LCS.regValue shmid)
    >>= AVC.resolveSymBV bak ?ptrWidth
  updateBoundsRefined resolveEffect
  shmIdBv <- maybe (CMC.throwM AE.SymbolicSharedMemorySegmentId)
                   pure
                   (WI.asBV shmIdSymBv)

  shmState <- use (LCS.stateContext . LCS.cruciblePersonality . AExt.sharedMemoryState)
  let lookupId = BVS.asUnsigned shmIdBv
  case AMS.sharedMemorySegmentAt lookupId shmState of
    Nothing -> liftIO $ LCB.addFailedAssertion bak $
       LCS.AssertFailureSimError ("Nonexistent shared memory ID: " ++ show lookupId)
                                 ""
    Just segment -> pure segment
  where
    -- Update the metric tracking the number of symbolic bitvector bounds
    -- refined
    updateBoundsRefined :: AVC.ResolveSymBVEffect -> m ()
    updateBoundsRefined resolveEffect =
      case resolveEffect of
        AVC.Concretized -> pure ()
        AVC.UnchangedBounds -> pure ()
        AVC.RefinedBounds ->
            LCS.stateContext
          . LCS.cruciblePersonality
          . AExt.simulationStats
          . AExt.lensNumBoundsRefined += 1



shmatOverride :: ( LCLM.HasLLVMAnn sym
                 , LCLM.HasPtrWidth w
                 , p ~ AExt.AmbientSimulatorState sym arch
                 , w ~ DMC.ArchAddrWidth arch
                 )
              => Syscall p
                         sym
                         (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                       Ctx.::> LCLM.LLVMPointerType w
                                       Ctx.::> LCLM.LLVMPointerType w)
                         ext
                         (LCLM.LLVMPointerType w)
shmatOverride =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "shmat" $ \bak args ->
    Ctx.uncurryAssignment (callShmat bak) args

-- | Override for the @shmget(2)@ syscall. It has the following caveats that may
-- need to be addressed in the future for a more faithful override:
--
-- * @key@ must be @IPC_PRIVATE@.
-- * @size@ is not rounded to a multiple of @PAGE_SIZE@ like it is in the real
--   implementation.
-- * @shmflag@ is ignored.  This is because:
--   * @key == IPC_PRIVATE@ implies that a shared memory segment is being
--     created regardless of whether the @IPC_CREAT@ flag is set.
--   * @key == IPC_PRIVATE@ always satisfies @IPC_EXCL@.
--   * @SHM_NORESERVE@ is irrelevant because we don't model swap space.
--   * The remaining flags concern page sizes and rounding modes, but this
--     override does not faithfully model the rounding behavior of @shmget@
-- * The shared memory IDs that this function returns start at 1 and increment
--   by 1 at each call.  This may differ from the real method of allocating
--   shared memory IDs.
callShmget :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              , LCLM.HasLLVMAnn sym
              , p ~ AExt.AmbientSimulatorState sym arch
              , w ~ DMC.ArchAddrWidth arch
              )
           => LCS.GlobalVar LCLM.Mem
           -> bak
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callShmget mvar bak key size _shmflag = do
  let ?memOpts = overrideMemOptions
  let sym = LCB.backendGetSym bak

  -- Extract and check that key is zero
  keyBv <- liftIO $ LCLM.projectLLVM_bv bak (LCS.regValue key)
  cond <- liftIO $ WI.bvEq sym keyBv =<< WI.bvLit sym ?ptrWidth (BVS.zero ?ptrWidth)
  liftIO $ LCB.assert bak cond (LCS.AssertFailureSimError
                                "Call to shmget() with non-zero key"
                                "")

  -- Allocate shared memory segment
  sizeBv <- liftIO $ LCLM.projectLLVM_bv bak (LCS.regValue size)
  let displayString = "<shared memory segment>"
  LCS.modifyGlobal mvar $ \mem -> do
    (segment, mem') <- liftIO $ LCLM.doMalloc bak
                                              LCLM.HeapAlloc
                                              LCLM.Mutable
                                              displayString
                                              mem
                                              sizeBv
                                              LCLD.noAlignment

    -- Store segment in the shared memory state and get an ID
    shmState <- use (LCS.stateContext . LCS.cruciblePersonality . AExt.sharedMemoryState)
    let (shmId, shmState') =
          AMS.newSharedMemorySegment segment shmState
    LCS.stateContext . LCS.cruciblePersonality . AExt.sharedMemoryState .= shmState'

    -- Convert ID to a BV
    shmIdBv <- liftIO $ WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth (AMS.asInteger shmId))
    shmIdPtr <- liftIO $ LCLM.llvmPointer_bv sym shmIdBv
    return (shmIdPtr, mem')

buildShmgetOverride :: ( LCLM.HasLLVMAnn sym
                       , LCLM.HasPtrWidth w
                       , p ~ AExt.AmbientSimulatorState sym arch
                       , w ~ DMC.ArchAddrWidth arch
                       )
                  => LCS.GlobalVar LCLM.Mem
                  -> Syscall p
                             sym
                             (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w)
                             ext
                             (LCLM.LLVMPointerType w)
buildShmgetOverride memVar =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "shmget" $ \bak args ->
    Ctx.uncurryAssignment (callShmget memVar bak) args

{- Note [Argument and Return Widths]

In the system call overrides we currently specify arguments and return types as
64 bit vectors.  However, for portability we may want to pass in the pointer
size as a repr.  On the other hand, many system calls logically restrict their
inputs and outputs to ranges smaller than those supported by register sized
values, so we also may want to more accurately capture those ranges.

-}
