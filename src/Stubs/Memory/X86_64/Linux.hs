{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}

module Stubs.Memory.X86_64.Linux (
    x86_64LinuxStmtExtensionOverride
  , x86_64LinuxInitGlobals
    -- * FSBASE and GSBASE
  , freshFSBaseGlobalVar
  , freshGSBaseGlobalVar
  ) where

import           Control.Lens ((^.))
import qualified Data.BitVector.Sized as BVS

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
  :: ( ?memOpts :: LCLM.MemOptions
     )
  => LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for FSBASE pointer
  -> LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for GSBASE pointer
  -> AM.InitArchSpecificGlobals DMX.X86_64
x86_64LinuxInitGlobals fsbaseGlob gsbaseGlob =
  AM.InitArchSpecificGlobals $ \bak mem0 -> do
    (fsbasePtr, mem1) <- initSegmentMemory bak mem0 "fs_array"
    (gsbasePtr, mem2) <- initSegmentMemory bak mem1 "gs_array"
    let globals0 = LCSG.insertGlobal fsbaseGlob fsbasePtr LCSG.emptyGlobals
    return (mem2, LCSG.insertGlobal gsbaseGlob gsbasePtr globals0)

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
