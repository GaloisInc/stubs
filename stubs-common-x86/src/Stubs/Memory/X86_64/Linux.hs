{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleContexts #-}

{-| Description: IsStubsMemoryModel instance for LLVMMemory with X86_64
-}
module Stubs.Memory.X86_64.Linux (
    x86_64LinuxStmtExtensionOverride
  , x86_64LinuxInitGlobals
    -- * FSBASE and GSBASE
  , freshFSBaseGlobalVar
  , freshGSBaseGlobalVar
  ) where

import           Control.Lens ((^.))
import qualified Data.BitVector.Sized as BVS
import           Data.Proxy (Proxy(..))

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.X86 as DMX
import qualified Data.Macaw.X86.Symbolic as DMXS
import qualified Data.Text as DT
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Common as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemType as LCLMT
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified What4.Interface as WI
import qualified What4.Symbol as WSym

import qualified Stubs.Memory as AM
import qualified Stubs.Panic as AP
import qualified Stubs.Memory as SM
import qualified Lang.Crucible.Types as LCT
import qualified Stubs.Common as SC
import qualified Data.Macaw.Symbolic.Memory.Lazy as DMSM
import qualified Data.Macaw.X86 as DMA
import qualified Data.Macaw.X86.Symbolic ()
import Control.Monad.IO.Class (liftIO, MonadIO)
import qualified Data.Parameterized.NatRepr as PN
import Stubs.Memory ()
import qualified Lang.Crucible.LLVM.MemModel.CallStack
import qualified Lang.Crucible.LLVM.Errors as LCLE
import qualified Lang.Crucible.LLVM.MemModel.Partial as LCLMP
import qualified Stubs.Memory.Common as SMC
import qualified Stubs.Logging as SL
import qualified Stubs.Extensions as SE
import qualified Data.Macaw.Symbolic as DMSMO
import qualified Data.Macaw.Symbolic.Memory as DMSMO
import qualified Stubs.Loader.BinaryConfig as SLB
import qualified Data.Macaw.BinaryLoader as DMB

instance SM.IsStubsMemoryModel DMS.LLVMMemory DMX.X86_64 where
  type instance PtrType DMS.LLVMMemory DMX.X86_64 =  LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64)
  type instance MemType DMS.LLVMMemory DMX.X86_64 = LCLM.Mem
  type instance BVToPtrTy w DMS.LLVMMemory DMX.X86_64 = LCLM.LLVMPointerType w
  type instance MemTable sym DMS.LLVMMemory DMX.X86_64 = DMSM.MemPtrTable sym 64
  type instance MemMap sym DMX.X86_64 = DMSMO.GlobalMap sym LCLM.Mem (DMC.ArchAddrWidth DMX.X86_64)
  type instance VerifierState sym DMS.LLVMMemory DMX.X86_64 = (SE.AmbientSimulatorState sym DMX.X86_64)

  ptrRepr = let ?ptrWidth=WI.knownRepr in LCLM.PtrRepr

  genExtImpl :: forall sym binfmt m. (DMB.BinaryLoader
                      DMA.X86_64 binfmt, Monad m, MonadIO m) => SC.Sym sym
    -> SM.InitialMemory sym DMSMO.LLVMMemory DMA.X86_64
    -> DMSMO.MacawArchEvalFn
      (SE.AmbientSimulatorState sym DMX.X86_64) sym (SM.MemType DMSMO.LLVMMemory DMA.X86_64) DMA.X86_64
    -> LCF.HandleAllocator
    -> DMS.GenArchVals DMS.LLVMMemory DMX.X86_64
    -> DMA.ArchitectureInfo DMX.X86_64
    -> SLB.BinaryConfig DMX.X86_64 binfmt
    -> SM.FunctionABI DMX.X86_64 sym (SE.AmbientSimulatorState sym DMX.X86_64) DMS.LLVMMemory
    -> SM.SyscallABI DMX.X86_64 sym (SE.AmbientSimulatorState sym DMX.X86_64)
    -> m (LCSE.ExtensionImpl (SE.AmbientSimulatorState sym DMX.X86_64) sym (DMSMO.MacawExt DMA.X86_64))
  genExtImpl (SC.Sym _ bak) initialMem f halloc archVals archInfo binconf functionABI syscallABI = do
    let ?memOpts = LCLM.defaultMemOptions
    (re, _) <- liftIO $ SM.buildRecordLLVMAnnotation @sym
    let ?recordLLVMAnnotation = re
    let ?processMacawAssert = DMSMO.defaultProcessMacawAssertion
    let mpt = SM.imMemTable initialMem
    let mmConf =
          (DMSM.memModelConfig bak mpt)
            { DMS.lookupFunctionHandle =
                SMC.symExLookupFunction SL.emptyLogger bak initialMem archVals binconf functionABI halloc archInfo Nothing

            , DMS.lookupSyscallHandle =
                SMC.symExLookupSyscall bak syscallABI halloc
            }
    return $ SE.ambientExtensions @sym @DMX.X86_64 bak f initialMem mmConf mempty

  bvToPtr :: LCT.TypeRepr tp -> LCT.TypeRepr (SM.ToPtrTy tp DMS.LLVMMemory DMX.X86_64)
  bvToPtr ty = case ty of
    -- Map BVRepr to LLVMPointerRepr...
    LCT.BVRepr n -> LCLM.LLVMPointerRepr n

    -- ...and map all other TypeReprs to themselves.
    LCT.AnyRepr -> LCT.AnyRepr
    LCT.UnitRepr -> LCT.UnitRepr
    LCT.BoolRepr -> LCT.BoolRepr
    LCT.IntegerRepr -> LCT.IntegerRepr
    LCT.NatRepr -> LCT.NatRepr
    LCT.RealValRepr -> LCT.RealValRepr
    LCT.ComplexRealRepr -> LCT.ComplexRealRepr
    LCT.CharRepr -> LCT.CharRepr
    LCT.FloatRepr r -> LCT.FloatRepr r
    LCT.IEEEFloatRepr r -> LCT.IEEEFloatRepr r
    LCT.MaybeRepr r -> LCT.MaybeRepr r
    LCT.VectorRepr r -> LCT.VectorRepr r
    LCT.SequenceRepr r -> LCT.SequenceRepr r
    LCT.StringRepr r -> LCT.StringRepr r
    LCT.StructRepr r -> LCT.StructRepr r
    LCT.VariantRepr r -> LCT.VariantRepr r
    LCT.IntrinsicRepr r1 r2 -> LCT.IntrinsicRepr r1 r2
    LCT.FunctionHandleRepr r1 r2 -> LCT.FunctionHandleRepr r1 r2
    LCT.RecursiveRepr r1 r2 -> LCT.RecursiveRepr r1 r2
    LCT.WordMapRepr r1 r2 -> LCT.WordMapRepr r1 r2
    LCT.SymbolicArrayRepr r1 r2 -> LCT.SymbolicArrayRepr r1 r2
    LCT.StringMapRepr r -> LCT.StringMapRepr r
    LCT.SymbolicStructRepr r -> LCT.SymbolicStructRepr r
    LCT.ReferenceRepr r -> LCT.ReferenceRepr r

  genStackPtr :: (Monad m, MonadIO m) => LCLM.LLVMPtr sym 64 -> WI.SymBV sym 64 -> SC.Sym sym -> m (LCLM.LLVMPtr sym 64)
  genStackPtr baseptr offset (SC.Sym sym _) = liftIO $ LCLM.ptrAdd sym WI.knownRepr baseptr offset

  insertStackPtr :: (WI.IsExprBuilder sym, LCB.IsSymInterface sym) => DMS.GenArchVals DMS.LLVMMemory DMX.X86_64 -> LCLM.LLVMPtr sym 64 -> LCS.RegEntry sym (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext DMX.X86_64))) -> LCS.RegEntry sym (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext DMX.X86_64)))
  insertStackPtr archVals sp initialRegsEntry= DMS.updateReg archVals initialRegsEntry DMC.sp_reg sp


  memPtrSize :: PN.NatRepr (DMC.ArchAddrWidth DMX.X86_64)
  memPtrSize = WI.knownRepr

  initMem :: SC.Sym sym -> DMA.ArchitectureInfo DMX.X86_64 -> Integer -> SLB.BinaryConfig DMX.X86_64 binfmt -> LCF.HandleAllocator -> (Monad m, MonadIO m) => m (SM.InitialMemory sym DMS.LLVMMemory DMX.X86_64)
  initMem (SC.Sym sym bak) archInfo stackSize binConf halloc = do

    let mems = fmap (DMB.memoryImage . SLB.lbpBinary) (SLB.bcBinaries binConf)
    let endian = DMSM.toCrucibleEndian (DMA.archEndianness archInfo)
    stackSizeBV <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackSize)
    let ?ptrWidth = SM.memPtrSize @DMS.LLVMMemory @DMX.X86_64
    (recordFn, _) <- liftIO SM.buildRecordLLVMAnnotation
    let ?recordLLVMAnnotation = recordFn
    let ?processMacawAssert = DMSMO.defaultProcessMacawAssertion
    let ?memOpts = LCLM.defaultMemOptions

    let supportedRelocs = SLB.bcSupportedRelocations binConf
    let globs = SLB.bcDynamicGlobalVarAddrs binConf
    (mem, memPtrTbl) <- DMSM.newMergedGlobalMemoryWith (SMC.globalMemoryHooks mems globs supportedRelocs) (Proxy @DMX.X86_64) bak endian DMSM.ConcreteMutable mems
    (stackBasePtr, mem1) <- liftIO $ LCLM.doMalloc bak LCLM.StackAlloc LCLM.Mutable "stack_alloc" mem stackSizeBV LCLD.noAlignment
    fsvar <- liftIO $ freshFSBaseGlobalVar halloc
    gsvar <- liftIO $ freshGSBaseGlobalVar halloc
    stackArrayStorage <- liftIO $ WI.freshConstant sym (WSym.safeSymbol "stack_array") WI.knownRepr
    mem2 <- liftIO $ LCLM.doArrayStore bak mem1 stackBasePtr LCLD.noAlignment stackArrayStorage stackSizeBV
    (mem3, globals0) <- liftIO $ x86_64LinuxInitGlobals fsvar gsvar (SC.Sym sym bak) mem2 LCSG.emptyGlobals
    memVar <- liftIO $ LCLM.mkMemVar (DT.pack "stubs::memory") halloc
    let globals1 = LCSG.insertGlobal memVar mem3 globals0

    let globalMap = DMSM.mapRegionPointers memPtrTbl
    return SM.InitialMemory{
      SM.imMemVar=memVar,
      SM.imGlobals=globals1,
      SM.imStackBasePtr=stackBasePtr,
      SM.imGlobalMap=globalMap,
      SM.imMemTable=memPtrTbl
    }

-- | Memory segment size in bytes
segmentSize :: Integer
segmentSize = 4 * 1024

-- | Offset base pointer should point to within a memory segment
segmentBaseOffset :: Integer
segmentBaseOffset = segmentSize `div` 2

-- | Create an initialize a new memory segment.
-- See @Note [x86_64 and TLS]@.
initSegmentMemory :: ( LCB.IsSymBackend sym bak
                     , LCLM.HasLLVMAnn sym
                     , DMSMO.MacawProcessAssertion sym
                     , ?memOpts :: LCLM.MemOptions
                     )
                  => bak
                  -> LCLM.MemImpl sym
                  -- ^ MemImpl to add the memory segment to
                  -> String
                  -- ^ Name for the array storage backing the new segment
                  -> IO ( LCLM.LLVMPtr sym (DMC.ArchAddrWidth DMX.X86_64)
                       -- Base pointer for new memory segment
                        , LCLM.MemImpl sym )
                       -- ^ Updated MemImpl containing new memory segment
initSegmentMemory bak mem0 symbol = do
  let sym = LCB.backendGetSym bak
  let ?ptrWidth = WI.knownRepr
  arrayStorage <- WI.freshConstant sym (WSym.safeSymbol symbol) WI.knownRepr
  segmentSizeBV <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr segmentSize)
  oneByte <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr 1)
  (segmentPtr, mem1) <-
    LCLM.doCalloc bak mem0 segmentSizeBV oneByte LCLD.noAlignment
  mem2 <- LCLM.doArrayStore bak
                            mem1
                            segmentPtr
                            LCLD.noAlignment
                            arrayStorage
                            segmentSizeBV

  -- See Note [x86_64 and TLS], point (1)
  segmentBaseOffsetBv <- WI.bvLit sym
                                  WI.knownRepr
                                  (BVS.mkBV WI.knownRepr segmentBaseOffset)
  basePtr <- LCLM.ptrAdd sym WI.knownRepr segmentPtr segmentBaseOffsetBv

  -- See Note [x86_64 and TLS], point (2)
  let memTy = LCLMT.PtrType LCLMT.VoidType
  let tpr = LCLM.LLVMPointerRepr ?ptrWidth
  sty <- LCLM.toStorableType memTy
  mem3 <- LCLM.doStore bak mem2 basePtr tpr sty LCLD.noAlignment basePtr

  return (basePtr, mem3)

-- | Allocate a fresh global variable representing FSBASE state.
freshFSBaseGlobalVar ::
  LCF.HandleAllocator ->
  IO (LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64)))
freshFSBaseGlobalVar hdlAlloc =
  LCCC.freshGlobalVar hdlAlloc
                      (DT.pack "fsbase")
                      (LCLM.LLVMPointerRepr (WI.knownNat @64))

-- | Allocate a fresh global variable representing GSBASE state.
freshGSBaseGlobalVar ::
  LCF.HandleAllocator ->
  IO (LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64)))
freshGSBaseGlobalVar hdlAlloc =
  LCCC.freshGlobalVar hdlAlloc
                      (DT.pack "gsbase")
                      (LCLM.LLVMPointerRepr (WI.knownNat @64))

-- | This function takes global variables for the FSBASE and GSBASE pointers
-- and returns an 'InitArchSpecificGlobals' that initializes those globals
-- and inserts them into the global variable state.
x86_64LinuxInitGlobals
  :: ( ?memOpts :: LCLM.MemOptions,
       ?recordLLVMAnnotation::Lang.Crucible.LLVM.MemModel.CallStack.CallStack -> LCLMP.BoolAnn sym -> LCLE.BadBehavior sym -> IO (),
       DMSMO.MacawProcessAssertion sym
     )
  => LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for FSBASE pointer
  -> LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for GSBASE pointer
  -> SC.Sym sym
  -> LCLM.MemImpl sym
  -> LCSG.SymGlobalState sym
  -> IO (LCLM.MemImpl sym, LCSG.SymGlobalState sym)
x86_64LinuxInitGlobals fsbaseGlob gsbaseGlob = \(SC.Sym _ bak) mem0 globals0 -> do
    (fsbasePtr, mem1) <- initSegmentMemory bak mem0 "fs_array"
    (gsbasePtr, mem2) <- initSegmentMemory bak mem1 "gs_array"
    let globals1 = LCSG.insertGlobal fsbaseGlob fsbasePtr globals0
    return (mem2, LCSG.insertGlobal gsbaseGlob gsbasePtr globals1)

-- | Return the value in a global variable.  This function panics if the
-- variable doesn't exist.
readGlobal :: LCCC.GlobalVar tp
           -- ^ Global variable to lookup
           -> LCSE.SimState p sym ext rtp g b
           -- ^ State containing the global
           -> LCS.RegValue sym tp
           -- ^ Value in the global
readGlobal global state =
  case LCSG.lookupGlobal global (state ^. LCSE.stateTree . LCSE.actFrame . LCSE.gpGlobals) of
    Nothing -> AP.panic AP.Memory
                        "readGlobal"
                        [ "Failed to find global variable: "
                          ++ show (LCCC.globalName global) ]
    Just ptr -> ptr

-- | Given global variables for the FSBASE and GSBASE pointers, returns a
-- MacawArchStmtExtensionOverride that properly handles reads from FSBASE and
-- GSBASE.
x86_64LinuxStmtExtensionOverride
  :: LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for FSBASE pointer
  -> LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for GSBASE pointer
  -> DMS.MacawArchStmtExtensionOverride DMX.X86_64
x86_64LinuxStmtExtensionOverride fsbaseGlobal gsbaseGlobal =
  DMS.MacawArchStmtExtensionOverride $ \stmt state -> do
    case stmt of
      DMXS.X86PrimFn fn ->
        case fn of
          DMX.ReadFSBase ->
            return (Just ((readGlobal fsbaseGlobal state), state))
          DMX.ReadGSBase ->
            return (Just ((readGlobal gsbaseGlobal state), state))
          _ -> -- Use default implementation for all other X86PrimFns
            return Nothing
      _ -> -- Use default implementation for all other statement types
        return Nothing

{-
Note [x86_64 and TLS]
~~~~~~~~~~~~~~~~~~~~~
x86 puts thread-local state (TLS) in the FS and GS segment registers. To model
this, we calloc a small allocation for each segment, and whenever macaw attempts
to read from FSBASE or GSBASE, it converts it into a read from the appropriate
allocation.

We have to do some work to make these pointers look like what C runtimes (e.g.,
glibc and musl) expect:

1. GCC generally appears to place TLS variables at negative offsets from
   FSBASE (for an example of this, see the generated 'fsbase.exe' test binary
   in 'tests/binaries/x86_64').  However, online code examples (such as
   https://unix.stackexchange.com/questions/453749/what-sets-fs0x28-stack-canary)
   also show GCC occasionally placing values at positive offsets from FSBASE.
   To support both cases, we put the segment base pointer in the middle of
   the allocation.

2. Functions that set `errno` will typically deference FSBASE and store a value
   into some offset from the dereferenced value. For examples of this, see
   the assembly for the `errno-glibc.exe` and `errno-musl.exe` binaries in
   `tests/binaries/x86_64`, which include `mov %fs:0x0,...` instructions.

   This happens because C runtimes usually store the `errno` (along with other
   TLS-related values) in a struct where the first field is a pointer to
   itself. For example, see how pthread_t is defined in musl:
   https://github.com/ifduyue/musl/blob/6d8a515796270eb6cec8a278cb353a078a10f09a/src/internal/pthread_impl.h#L19-L21
   If the comments in that code are to be believed, this convention is part of
   the ABI, so other C runtimes like glibc also follow this convention. (Some
   local experimentation with glibc binaries confirms this to be the case.)

   To accommodate this pattern, whenever we calloc a base pointer in the
   verifier, we also store the pointer into the `self` pointer field of the
   ABI-mandated struct, which happens to be the first field. That way,
   instructions like `mov %fs:0x0,...` will successfully dereference the
   pointer, and offsets from the derefenced value will return symbolic bytes,
   as expected.
-}
