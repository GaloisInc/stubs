{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | Defines verifier-specific extensions for Macaw's simulation functionality.
module Stubs.Extensions
  ( ambientExtensions,
  readMem
  , resolveAndPopulate
  , loadString
  , loadConcreteString
  , storeString
  , storeConcreteString
  ,AmbientSimulatorState(..)
  , incrementSimStat
  , lensNumOvsApplied
  , lensNumBoundsRefined
  , AmbientSimulationStats(..)
  , emptyAmbientSimulatorState
  , functionOvHandles
  , functionAddrOvHandles
  , syscallOvHandles
  , discoveredFunctionHandles
  , simulationStats
  , overrideLookupFunctionHandle
  , sharedMemoryState
  , macawLazySimulatorState
  ) where

import qualified Control.Exception as X
import           Control.Lens ( Lens', (^.), lens, (&), (+~))
import           Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Control.Monad.State as CMS
import qualified Data.Aeson as DA
import qualified Data.BitVector.Sized as BV
import qualified Data.Map.Strict as Map
import           Data.Maybe ( isNothing )
import qualified Data.Parameterized.Map as MapF
import           Data.Word ( Word8 )
import           GHC.Generics ( Generic )
import qualified GHC.Stack as GHC

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Memory.Lazy as DMSM
import qualified Data.Macaw.Symbolic.Backend as DMSB
import qualified Data.Macaw.Symbolic.MemOps as DMSMO
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LCLMP
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Exception as AE
import qualified Stubs.Memory.SharedMemory as AMS
import qualified Stubs.Verifier.Concretize as AVC
import qualified Stubs.Syscall as ASy
import qualified Stubs.FunctionOverride as AF
import qualified Lang.Crucible.LLVM.MemModel.CallStack
import qualified Lang.Crucible.LLVM.MemModel.Partial as LCLMP
import qualified Lang.Crucible.LLVM.Errors as LCLE
import qualified Stubs.Memory as SM
-- | Return @ambient-verifier@ extension evaluation functions.
ambientExtensions ::
     forall sym arch bak scope st fs solver w. ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , SM.MemType DMS.LLVMMemory arch ~ LCLM.Mem, SM.IsStubsMemoryModel DMS.LLVMMemory arch
     , SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w, SM.PtrType DMS.LLVMMemory arch ~ LCLMP.LLVMPointerType w
     , SM.MemTable sym DMS.LLVMMemory arch ~ DMSM.MemPtrTable sym (DMC.ArchAddrWidth arch)
     ,?memOpts::LCLM.MemOptions
     ,?recordLLVMAnnotation::Lang.Crucible.LLVM.MemModel.CallStack.CallStack
                                           -> LCLMP.BoolAnn sym
                                           -> LCLE.BadBehavior sym
                                           -> IO ()
     )
  => bak
  -> DMS.MacawArchEvalFn (AmbientSimulatorState sym arch) sym LCLM.Mem arch
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -- ^ Initial memory state for symbolic execution
  -> DMS.MemModelConfig (AmbientSimulatorState sym arch) sym arch LCLM.Mem
  -- ^ Configuration options for the memory model
  -> Map.Map (DMM.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> LCSE.ExtensionImpl (AmbientSimulatorState sym arch) sym (DMS.MacawExt arch)
ambientExtensions bak f initialMem mmConf unsupportedRelocs =
  (DMS.macawExtensions f (SM.imMemVar initialMem) mmConf)
    { LCSE.extensionEval = \_sym iTypes logFn cst g ->
        evalMacawExprExtension bak f initialMem mmConf iTypes logFn cst g
    , LCSE.extensionExec =
        execAmbientStmtExtension bak f initialMem mmConf unsupportedRelocs
    }

-- -- | This function proceeds in two steps:
-- --
-- -- 1.  If the input pointer is a global pointer (the block ID of the pointer is
-- --     zero), it is translated into an LLVM pointer.  If the input pointer is
-- --     not a global pointer then it has already been translated into an LLVM
-- --     pointer and this step is a no-op.  For more information on this process,
-- --     see the @tryGlobPointer@ documentation in "Data.Macaw.Symbolic.MemOps".
-- --
-- -- 2.  The LLVM pointer from step 1 is then resolved to a concrete pointer if
-- --     possible.  For more information, see the documentation on
-- --     @resolveSingletonPointer@ in "Ambient.Verifier.Concretize".
-- --
-- -- This function returns the resolved pointer from step 2 and an
-- -- 'AVC.ResolveSymBVEffect' explaining the outcome of the resolution process.
resolvePointer
  :: ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , 1 WI.<= w )
  => bak
  -> LCLM.MemImpl sym
  -> DMS.GlobalMap sym LCLM.Mem w
  -- ^ Global map to use for translation
  -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
  -- ^ Pointer to resolve
  -> IO (LCLM.LLVMPtr sym w, AVC.ResolveSymBVEffect)
resolvePointer bak memImpl globMap (LCS.regValue -> ptr) =
  DMSMO.tryGlobPtr bak memImpl globMap ptr >>= AVC.resolveSingletonPointer bak

-- | Resolve a pointer using the process described in the 'resolvePointer'
-- documentation, then initialize the region of memory in the SMT array the
-- pointer points to.  See @Note [Lazy memory initialization]@ in
-- "Ambient.Extensions.Memory".
--
-- This function returns the resolved pointer and an updated state.  It also
-- updates the metric tracking the number of symbolic bitvector bounds in the
-- returned state.
resolveAndPopulate
  :: ( sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , p ~ AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     , LCB.IsSymInterface sym
     , WPO.OnlineSolver solver
     , DMM.MemWidth w, SM.IsStubsMemoryModel DMS.LLVMMemory arch
     , SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w
     )
  => bak
  -> LCLM.MemImpl sym
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -> WI.SymBV sym w
  -- ^ The amount of memory to read
  -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
  -> LCS.SimState p sym ext rtp f args
  -> IO (LCLM.LLVMPtr sym w, LCS.SimState p sym ext rtp f args)
resolveAndPopulate bak memImpl initialMem _readSizeBV ptr st = do
  (ptr', _resolveEffect) <-
      resolvePointer bak memImpl (SM.imGlobalMap initialMem) ptr
  -- st' <- lazilyPopulateGlobalMemArr bak
  --                                   (AM.imMemPtrTable initialMem) -- will maybe be an issue
  --                                   readSizeBV
  --                                   ptr'
  --                                   st
  return (ptr', st)

-- | Read memory through a pointer
readMem :: forall sym scope st fs bak solver arch p w ext rtp f args ty.
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , LCLM.HasLLVMAnn sym
     , p ~ AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , ?memOpts :: LCLM.MemOptions
     , SM.IsStubsMemoryModel DMS.LLVMMemory arch ,
     SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w,
     SM.MemTable sym DMS.LLVMMemory arch ~ DMSM.MemPtrTable sym (DMC.ArchAddrWidth arch)
     )
  => bak
  -> LCLM.MemImpl sym
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -- ^ Initial memory state for symbolic execution
  -> DMS.MemModelConfig (AmbientSimulatorState sym arch) sym arch LCLM.Mem
  -- ^ Configuration options for the memory model
  -> Map.Map (DMM.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> LCS.SimState p sym ext rtp f args
  -> DMM.AddrWidthRepr w
  -> DMC.MemRepr ty
  -- ^ Info about read (endianness, size)
  -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
  -- ^ Pointer to read from
  -> IO ( LCS.RegValue sym (DMS.ToCrucibleType ty)
        , LCS.SimState p sym ext rtp f args )
readMem bak memImpl initialMem mmConf unsupportedRelocs st addrWidth memRep ptr0 =
  DMM.addrWidthClass addrWidth $ do
    let sym = LCB.backendGetSym bak
    (ptr1, resolveEffect) <-
        resolvePointer bak memImpl (SM.imGlobalMap initialMem) ptr0
    assertRelocSupported ptr1 unsupportedRelocs
    mbReadVal <- DMS.concreteImmutableGlobalRead mmConf memRep ptr1
    case mbReadVal of
      Just readVal -> do
        let st' = incrementSimStat lensNumReads st
        pure (readVal, st')
      Nothing -> do
        let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerRead
        mGlobalPtrValid <- (\_ _ _ _->return Nothing) sym puse Nothing ptr0
        case mGlobalPtrValid of
          Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
          Nothing -> return ()
        readVal <- DMSMO.doReadMem bak memImpl addrWidth memRep ptr1
        let st2 = updateReads readVal memRep (updateBoundsRefined resolveEffect st)
        return (readVal,st2)

-- | Write memory to a pointer
writeMem :: forall sym scope st fs bak solver arch p w ext rtp f args ty.
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , LCLM.HasLLVMAnn sym
     , p ~ AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     , ?memOpts :: LCLM.MemOptions
     , SM.IsStubsMemoryModel DMS.LLVMMemory arch
     , SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w
     )
  => bak
  -> LCLM.MemImpl sym
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -- ^ Initial memory state for symbolic execution
  -> LCS.SimState p sym ext rtp f args
  -> DMM.AddrWidthRepr w
  -> DMC.MemRepr ty
  -- ^ Info about write (endianness, size)
  -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
  -- ^ Pointer to write to
  -> LCS.RegEntry sym (DMS.ToCrucibleType ty)
  -- ^ Value to write
  -> IO ( LCLM.MemImpl sym
        , LCS.SimState p sym ext rtp f args )
writeMem bak memImpl initialMem st addrWidth memRep ptr0 v =
  DMM.addrWidthClass addrWidth $ do
    let sym = LCB.backendGetSym bak
    let w = DMM.memWidthNatRepr
    memReprBytesBV <- WI.bvLit sym w $ BV.mkBV w $
                      toInteger $ DMC.memReprBytes memRep
    (ptr1, st1) <- resolveAndPopulate bak memImpl initialMem memReprBytesBV ptr0 st
    mGlobalPtrValid <- return Nothing
    case mGlobalPtrValid of
      Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
      Nothing -> return ()
    mem1 <- DMSMO.doWriteMem bak memImpl addrWidth memRep ptr1 (LCS.regValue v)
    pure (mem1, st1)

-- | Load a null-terminated string from the memory.

-- The pointer to read from must be concrete and nonnull. We allow symbolic
-- characters, but we require that the string end with a concrete null
-- terminator character. Otherwise it is very difficult to tell when the string
-- has terminated. If a maximum number of characters is provided, no more
-- than that number of charcters will be read.  In either case,
-- 'loadString' will stop reading if it encounters a null-terminator.

-- NOTE: The only differences between this function and the version defined in
-- Crucible is that this function:

-- * Uses the Ambient @readMem@ function to load through the string pointer

-- * Permits symbolic characters
loadString
  :: forall sym bak w p ext r args ret m arch scope st fs solver
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , GHC.HasCallStack
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     , p ~ AmbientSimulatorState sym arch
     , m ~ LCS.OverrideSim p sym ext r args ret
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver, SM.IsStubsMemoryModel DMS.LLVMMemory arch
     , SM.MemTable sym DMS.LLVMMemory arch ~ DMSM.MemPtrTable sym (DMC.ArchAddrWidth arch)
     , SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w
     )
  => bak
  -> LCLM.MemImpl sym
  -- ^ memory to read from
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -- ^ Initial memory state for symbolic execution
  -> DMS.MemModelConfig (AmbientSimulatorState sym arch) sym arch LCLM.Mem
  -- ^ Configuration options for the memory model
  -> Map.Map (DMC.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
  -- ^ pointer to string value
  -> Maybe Int
  -- ^ maximum characters to read
  -> m [WI.SymBV sym 8]
loadString bak memImpl initialMem mmConf unsupportedRelocs = go id
 where
  sym = LCB.backendGetSym bak

  go :: ([WI.SymBV sym 8] -> [WI.SymBV sym 8])
     -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
     -> Maybe Int
     -> m [WI.SymBV sym 8]
  go f _ (Just 0) = return $ f []
  go f p maxChars = do
     let readInfo = DMC.BVMemRepr (WI.knownNat @1) DMC.LittleEndian
     st <- CMS.get
     (v, st') <- liftIO $ readMem bak memImpl initialMem mmConf unsupportedRelocs st (DMC.addrWidthRepr ?ptrWidth) readInfo p
     CMS.put st'
     x <- liftIO $ LCLM.projectLLVM_bv bak v
     if (BV.asUnsigned <$> WI.asBV x) == Just 0
       then return $ f [] -- We have encountered a null terminator, so stop.
       else do
         p' <- liftIO $ LCLM.doPtrAddOffset bak memImpl (LCS.regValue p) =<< WI.bvLit sym LCLM.PtrWidth (BV.one LCLM.PtrWidth)
         go (f . (x:)) (LCS.RegEntry (LCLM.LLVMPointerRepr ?ptrWidth) p') (fmap (\n -> n - 1) maxChars)

-- | Like 'loadString', except that each character read is asserted to be
-- concrete. If a symbolic character is encountered, this function will
-- generate a failing assertion.
loadConcreteString
  :: forall sym bak w p ext r args ret m arch scope st fs solver
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , GHC.HasCallStack
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     , p ~ AmbientSimulatorState sym arch
     , m ~ LCS.OverrideSim p sym ext r args ret
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver, SM.IsStubsMemoryModel DMS.LLVMMemory arch
     , SM.MemTable sym DMS.LLVMMemory arch ~ DMSM.MemPtrTable sym (DMC.ArchAddrWidth arch)
     , SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w
     )
  => bak
  -> LCLM.MemImpl sym
  -- ^ memory to read from
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -- ^ Initial memory state for symbolic execution
  -> DMS.MemModelConfig (AmbientSimulatorState sym arch) sym arch LCLM.Mem
  -- ^ Configuration options for the memory model
  -> Map.Map (DMC.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
  -- ^ pointer to string value
  -> Maybe Int
  -- ^ maximum characters to read
  -> m [Word8]
loadConcreteString bak memImpl initialMem mmConf unsupportedRelocs p maxChars = do
  symBytes <- loadString bak memImpl initialMem mmConf unsupportedRelocs p maxChars
  traverse concretizeByte symBytes
  where
    concretizeByte :: WI.SymBV sym 8 -> m Word8
    concretizeByte symByte =
      case BV.asUnsigned <$> WI.asBV symByte of
        Just byte -> pure $ fromInteger byte
        Nothing ->
          liftIO $ LCB.addFailedAssertion bak
                 $ LCS.Unsupported GHC.callStack
                     "Symbolic value encountered when loading a string"

-- | Store a string (represented as a list of bytes) to memory,
-- including a null terminator at the end. We permit symbolic bytes, but the
-- null terminator written at the end will always be concrete.
storeString
  :: forall sym bak w p ext r args ret m arch scope st fs solver
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , GHC.HasCallStack
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     , p ~ AmbientSimulatorState sym arch
     , m ~ LCS.OverrideSim p sym ext r args ret
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , SM.IsStubsMemoryModel DMS.LLVMMemory arch
     , SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w
     )
  => bak
  -> LCLM.MemImpl sym
  -- ^ Memory to write to
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -- ^ Initial memory state for symbolic execution
  -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
  -- ^ Pointer to write value to
  -> [WI.SymBV sym 8]
  -- ^ The bytes of the string to write (null terminator not included)
  -> m (LCLM.MemImpl sym)
  -- ^ The updated memory
storeString bak memImpl initialMem = go memImpl
  where
    sym = LCB.backendGetSym bak
    writeInfo = DMC.BVMemRepr (WI.knownNat @1) DMC.LittleEndian
    byteRepr = WI.knownNat @8

    go :: LCLM.MemImpl sym -> LCS.RegEntry sym (LCLM.LLVMPointerType w) -> [WI.SymBV sym 8] -> m (LCLM.MemImpl sym)
    go mem p bytes
      = case bytes of
          [] -> do
            bvNullTerminator <- liftIO $ WI.bvLit sym byteRepr $ BV.zero byteRepr
            writeByte mem p bvNullTerminator

          (bvByte:bs) -> do
            mem' <- writeByte mem p bvByte
            bvOne <- liftIO $ WI.bvLit sym LCLM.PtrWidth (BV.one LCLM.PtrWidth)
            p' <- liftIO $ LCLM.doPtrAddOffset bak mem' (LCS.regValue p) bvOne
            go mem' (LCS.RegEntry (LCLM.LLVMPointerRepr ?ptrWidth) p') bs

    writeByte :: LCLM.MemImpl sym -> LCS.RegEntry sym (LCLM.LLVMPointerType w) -> WI.SymBV sym 8 -> m (LCLM.MemImpl sym)
    writeByte mem p bvByte = do
      ptrByte <- liftIO $ LCLM.llvmPointer_bv sym bvByte
      let ptrByte' = LCS.RegEntry (LCLM.LLVMPointerRepr byteRepr) ptrByte
      st <- CMS.get
      (mem', st') <- liftIO $
        writeMem bak mem initialMem st (DMC.addrWidthRepr ?ptrWidth) writeInfo p ptrByte'
      CMS.put st'
      pure mem'

-- | Like 'storeString', except that each character in the string is concrete.
storeConcreteString
  :: forall sym bak w p ext r args ret m arch scope st fs solver
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , GHC.HasCallStack
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     , p ~ AmbientSimulatorState sym arch
     , m ~ LCS.OverrideSim p sym ext r args ret
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , SM.IsStubsMemoryModel DMS.LLVMMemory arch
     , SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w
     )
  => bak
  -> LCLM.MemImpl sym
  -- ^ Memory to write to
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -- ^ Initial memory state for symbolic execution
  -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
  -- ^ Pointer to write value to
  -> [Word8]
  -- ^ The bytes of the string to write (null terminator not included)
  -> m (LCLM.MemImpl sym)
  -- ^ The updated memory
storeConcreteString bak memImpl initialMem p bytes = do
  symBytes <- liftIO $
    traverse (WI.bvLit sym byteRepr . BV.mkBV byteRepr . toInteger) bytes
  storeString bak memImpl initialMem p symBytes
  where
    sym = LCB.backendGetSym bak
    byteRepr = WI.knownNat @8

-- | This evaluates a Macaw expression extension in the simulator.
--
-- Currently, this simply uses the default implementation provided by
-- 'DMS.macawExtensions'. We keep this around in case we want to override
-- specific 'DMS.MacawExprExtension's (e.g., 'DMS.PtrToBits) for debugging
-- purposes.
evalMacawExprExtension ::
     forall sym scope st fs bak solver arch p w f tp rtp blocks r ctx
  .  ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , LCLM.HasLLVMAnn sym
     , p ~ AmbientSimulatorState sym arch
     , ?memOpts :: LCLM.MemOptions
     , w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , SM.PtrType DMS.LLVMMemory arch ~ LCLMP.LLVMPointerType w, SM.IsStubsMemoryModel DMS.LLVMMemory arch
     , SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w
     , SM.MemType DMS.LLVMMemory arch ~ LCLM.Mem
     )
  => bak
  -> DMS.MacawArchEvalFn (AmbientSimulatorState sym arch) sym LCLM.Mem arch
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -- ^ Initial memory state for symbolic execution
  -> DMS.MemModelConfig (AmbientSimulatorState sym arch) sym arch LCLM.Mem
  -- ^ Configuration options for the memory model
  -> LCS.IntrinsicTypes sym
  -> (Int -> String -> IO ())
  -> LCS.CrucibleState p sym (DMS.MacawExt arch) rtp blocks r ctx
  -> (forall utp . f utp -> IO (LCS.RegValue sym utp))
  -> DMS.MacawExprExtension arch f tp
  -> IO (LCS.RegValue sym tp)
evalMacawExprExtension bak f initialMem mmConf iTypes logFn cst g e0 =
  case e0 of
    DMS.PtrToBits xw xv -> do
      x <- g xv
      let defaultBehavior = DMSMO.doPtrToBits sym x
      -- If the pointer argument has a special region number, then don't bother
      -- checking if the region is equal to zero.
      -- See Note [Special pointer region numbers].
      -- Note that a special pointer must be as wide as the architecture width,
      -- which is why it is admissable to use testEquality like it is used
      -- below.
      case WI.testEquality (DMC.memWidthNatRepr @w) xw of
        Just WI.Refl -> do
          xSpecial <- hasSpecialPointerRegion sym initialMem x
          if xSpecial
            then pure $ LCLMP.llvmPointerOffset x
            else defaultBehavior
        Nothing -> defaultBehavior
    _ ->
      LCSE.extensionEval (DMS.macawExtensions f mvar mmConf)
                         bak iTypes logFn cst g e0
  where
    sym = LCB.backendGetSym bak
    mvar = SM.imMemVar initialMem

-- | This evaluates a Macaw statement extension in the simulator.
execAmbientStmtExtension :: forall sym scope st fs bak solver arch p w.
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , LCLM.HasLLVMAnn sym
     , p ~ AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     , ?memOpts :: LCLM.MemOptions
     , DMM.MemWidth w
     , SM.MemType DMS.LLVMMemory arch ~ LCLM.Mem
     ,SM.IsStubsMemoryModel DMS.LLVMMemory arch,
     SM.PtrType DMS.LLVMMemory arch ~ LCLM.LLVMPointerType (DMC.ArchAddrWidth arch)
     , SM.MemTable sym DMS.LLVMMemory arch ~ DMSM.MemPtrTable sym (DMC.ArchAddrWidth arch)
     , SM.MemMap sym arch ~ DMSMO.GlobalMap sym LCLM.Mem w
     )
  => bak
  -> DMS.MacawArchEvalFn p sym LCLM.Mem arch
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -- ^ Initial memory state for symbolic execution
  -> DMS.MemModelConfig (AmbientSimulatorState sym arch) sym arch LCLM.Mem
  -- ^ Configuration options for the memory model
  -> Map.Map (DMM.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> DMSB.MacawEvalStmtFunc (DMS.MacawStmtExtension arch) p sym (DMS.MacawExt arch)
execAmbientStmtExtension bak f initialMem mmConf unsupportedRelocs s0 st =
  -- NB: Most of this code is copied directly from the 'execMacawStmtExtension'
  -- function in macaw-symbolic. One notable difference is the use of
  -- 'AVC.resolveSingletonPointer' to attempt to concrete the pointer being
  -- read from—or, the pointer being written to—in cases relating to
  -- reading or writing memory, respectively.
  case s0 of
    DMS.MacawReadMem addrWidth memRep ptr0 -> do
      memImpl <- DMSMO.getMem st mvar
      readMem bak memImpl initialMem mmConf unsupportedRelocs st addrWidth memRep ptr0
    DMS.MacawCondReadMem addrWidth memRep cond ptr0 condFalseValue -> DMM.addrWidthClass addrWidth $ do
      memImpl <- DMSMO.getMem st mvar
      (ptr1, resolveEffect) <- resolvePointer bak memImpl globs ptr0
      assertRelocSupported ptr1 unsupportedRelocs
      mbReadVal <- DMS.concreteImmutableGlobalRead mmConf memRep ptr1
      case mbReadVal of
        Just readVal -> do
          readVal' <- DMSMO.muxMemReprValue sym memRep (LCS.regValue cond) readVal (LCS.regValue condFalseValue)
          let st' = incrementSimStat lensNumReads st
          pure (readVal', st')
        Nothing -> do
          st1 <- DMS.lazilyPopulateGlobalMem mmConf memRep ptr1 st
          let puse = DMS.PointerUse (st1 ^. LCSE.stateLocation) DMS.PointerRead
          mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
          case mGlobalPtrValid of
            Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
            Nothing -> return ()
          readVal <- DMSMO.doCondReadMem bak memImpl addrWidth memRep (LCS.regValue cond) ptr1 (LCS.regValue condFalseValue)
          let st2 = updateReads readVal memRep (updateBoundsRefined resolveEffect st1)
          return (readVal,st2)
    DMS.MacawWriteMem addrWidth memRep ptr0 v -> DMM.addrWidthClass addrWidth $ do
      memImpl <- DMSMO.getMem st mvar
      (memImpl', st') <- writeMem bak memImpl initialMem st addrWidth memRep ptr0 v
      pure ((), DMSMO.setMem st' mvar memImpl')
    DMS.MacawCondWriteMem addrWidth memRep cond ptr0 v -> DMM.addrWidthClass addrWidth $ do
      memImpl <- DMSMO.getMem st mvar
      let w = DMM.memWidthNatRepr
      memReprBytesBV <- WI.bvLit sym w $ BV.mkBV w $
                        toInteger $ DMC.memReprBytes memRep
      (ptr1, st1) <- resolveAndPopulate bak memImpl initialMem memReprBytesBV ptr0 st
      let puse = DMS.PointerUse (st1 ^. LCSE.stateLocation) DMS.PointerWrite
      mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      mem1 <- DMSMO.doCondWriteMem bak memImpl addrWidth memRep (LCS.regValue cond) ptr1 (LCS.regValue v)
      pure ((), DMSMO.setMem st1 mvar mem1)
    DMS.PtrEq w xEntry yEntry -> do
      let x = LCS.regValue xEntry
      let y = LCS.regValue yEntry
      xSpecial <- hasSpecialPointerRegion sym initialMem x
      ySpecial <- hasSpecialPointerRegion sym initialMem y
      -- If one of the pointers has a special region number, then don't bother
      -- checking the region numbers for equality.
      -- See Note [Special pointer region numbers].
      if xSpecial || ySpecial
        then do eq <- WI.bvEq sym (LCLMP.llvmPointerOffset x)
                                  (LCLMP.llvmPointerOffset y)
                pure (eq, st)
        else DMSMO.doPtrEq st mvar w xEntry yEntry
    _ ->
      LCSE.extensionExec (DMS.macawExtensions f mvar mmConf) s0 st
  where
    sym = LCB.backendGetSym bak
    mvar = SM.imMemVar initialMem
    globs = SM.imGlobalMap initialMem

    toMemPred :: DMS.MkGlobalPointerValidityAssertion sym w
    toMemPred = (\_ _ _ _->return Nothing)

-- | Check if a pointer has a special region number. Currently, the only such
-- special region number is that of the stack pointer.
-- See Note [Special pointer region numbers].
hasSpecialPointerRegion ::
     (LCB.IsSymInterface sym,
     SM.IsStubsMemoryModel DMS.LLVMMemory arch,
     SM.PtrType DMS.LLVMMemory arch ~ LCLM.LLVMPointerType (DMC.ArchAddrWidth arch)
     )
  => sym
  -> SM.InitialMemory sym DMS.LLVMMemory arch
  -> LCLM.LLVMPtr sym w
  -> IO Bool
hasSpecialPointerRegion sym initialMem ptr = do
  eq <- WI.natEq sym (LCLMP.llvmPointerBlock (SM.imStackBasePtr initialMem))
                     (LCLMP.llvmPointerBlock ptr)
  case WI.asConstantPred eq of
    Just b  -> pure b
    Nothing -> pure False
-- Update the metrics tracking the total number of reads and number of
-- symbolic reads
updateReads :: forall sym ty p ext rtp f args arch
             . ( p ~ AmbientSimulatorState sym arch
               , LCB.IsSymInterface sym )
            => LCS.RegValue sym (DMS.ToCrucibleType ty)
            -- ^ Value returned by a read
            -> DMC.MemRepr ty
            -- ^ Type of the read value
            -> LCS.SimState p sym ext rtp f args
            -- ^ State to update
            -> LCS.SimState p sym ext rtp f args
updateReads readVal memRep state =
  let state' = incrementSimStat lensNumReads state in
  if readIsSymbolic memRep readVal
  then incrementSimStat lensNumSymbolicReads state'
  else state'
  where
    -- Returns True iff the memory read is at least partly symbolic
    readIsSymbolic :: DMC.MemRepr ty'
                   -> LCS.RegValue sym (DMS.ToCrucibleType ty')
                   -> Bool
    readIsSymbolic memRep' readVal' =
      case memRep' of
        DMC.BVMemRepr{} ->
          -- Check whether value is symbolic
          let (LCLM.LLVMPointer base bv) = readVal' in
          isNothing (WI.asNat base) || isNothing (WI.asBV bv)
        DMC.FloatMemRepr{} -> isNothing (WI.asConcrete readVal')
        DMC.PackedVecMemRepr _w vecMemRep ->
          -- Recursively look for symbolic values in vector
          any (readIsSymbolic vecMemRep) readVal'

-- Update the metric tracking the number of symbolic bitvector bounds
-- refined
updateBoundsRefined :: ( p ~ AmbientSimulatorState sym arch )
                    => AVC.ResolveSymBVEffect
                    -- ^ Effect resolving SymBV had on underlying bitvector
                    -> LCS.SimState p sym ext rtp f args
                    -- ^ State to update
                    -> LCS.SimState p sym ext rtp f args
updateBoundsRefined resolveEffect state =
  case resolveEffect of
    AVC.Concretized -> state
    AVC.UnchangedBounds -> state
    AVC.RefinedBounds -> incrementSimStat lensNumBoundsRefined state

-- | Check whether a pointer points to a relocation address, and if so,
-- assert that the underlying relocation type is supported.  If not, throw
-- an UnsupportedRelocation exception.  This is a best effort attempt: if
-- the read is symbolic the check is skipped.
assertRelocSupported :: (LCB.IsSymInterface sym, DMM.MemWidth w)
                     => LCLM.LLVMPtr sym w
                     -> Map.Map (DMM.MemWord w) String
                     -- ^ Mapping from unsupported relocation addresses to the
                     -- names of the unsupported relocation types.
                     -> IO ()
assertRelocSupported (LCLM.LLVMPointer _base offset) unsupportedRelocs =
  case WI.asBV offset of
    Nothing ->
      -- Symbolic read.  Cannot check whether this is an unsupported
      -- relocation.
      return ()
    Just bv -> do
      -- Check whether this read is from an unsupported relocation type.
      let addr = DMM.memWord (fromIntegral (BV.asUnsigned bv))
      case Map.lookup addr unsupportedRelocs of
        Just relTypeName ->
          X.throwIO $ AE.UnsupportedRelocation relTypeName
        Nothing -> return ()

-- | Statistics gathered during simulation
data AmbientSimulationStats = AmbientSimulationStats
  { numOvsApplied :: Integer
  -- ^ The total number of times overrides were applied during symbolic
  -- execution
  , numReads :: Integer
  -- ^ Total number of memory reads during simulation
  , numBoundsRefined :: Integer
  -- ^ Total number of symbolic bitvector bounds refined
  , numSymbolicReads :: Integer
  -- ^ Total number of memory reads that are at least partly symbolic
  }
  deriving ( Generic )
instance DA.ToJSON AmbientSimulationStats

emptyAmbientSimulationStats :: AmbientSimulationStats
emptyAmbientSimulationStats =
  AmbientSimulationStats { numOvsApplied = 0
                         , numReads = 0
                         , numBoundsRefined = 0
                         , numSymbolicReads = 0
                         }

-- | Increment a counter in the 'AmbientSimulationStats' held in a given
-- crucible state.
incrementSimStat :: ( p ~ AmbientSimulatorState sym arch )
                 => Lens' AmbientSimulationStats Integer
                 -- ^ Accessor for the stat to update
                 -> LCS.SimState p sym ext rtp f args
                 -- ^ State holding the 'AmbientSimulationStats' to update
                 -> LCS.SimState p sym ext rtp f args
incrementSimStat statLens state =
  state & LCS.stateContext
        . LCS.cruciblePersonality
        . simulationStats
        . statLens +~ 1

lensNumOvsApplied :: Lens' AmbientSimulationStats Integer
lensNumOvsApplied = lens numOvsApplied (\s v -> s { numOvsApplied = v })

lensNumReads :: Lens' AmbientSimulationStats Integer
lensNumReads = lens numReads (\s v -> s { numReads = v })

lensNumBoundsRefined :: Lens' AmbientSimulationStats Integer
lensNumBoundsRefined = lens numBoundsRefined (\s v -> s { numBoundsRefined = v })

lensNumSymbolicReads :: Lens' AmbientSimulationStats Integer
lensNumSymbolicReads = lens numSymbolicReads (\s v -> s { numSymbolicReads = v })

-- | The state extension for Crucible holding verifier-specific state.
data AmbientSimulatorState sym arch = AmbientSimulatorState
  { _functionOvHandles :: Map.Map WF.FunctionName (AF.FunctionOverrideHandle arch)
    -- ^ A map from registered function override names to their handles.
    -- See @Note [Lazily registering overrides]@.
  , _functionAddrOvHandles :: Map.Map (AF.FunctionAddrLoc (DMC.ArchAddrWidth arch))
                                      (AF.FunctionOverrideHandle arch)
    -- ^ A map from function overrides at particular addresses to their handles.
    -- See @Note [Lazily registering overrides]@.
  , _syscallOvHandles :: MapF.MapF ASy.SyscallNumRepr ASy.SyscallFnHandle
    -- ^ A map from registered syscall overrides to their handles.
    -- See @Note [Lazily registering overrides]@.
  , _discoveredFunctionHandles :: Map.Map (DMC.ArchSegmentOff arch) (AF.FunctionOverrideHandle arch)
    -- ^ A map of discovered functions to their handles.
    -- See @Note [Incremental code discovery]@.
    --
    -- Note that this puts every address from all binaries' address spaces into
    -- a single map. This happens to work today since we ensure that the
    -- address spaces in each binary are disjoint from each other (see
    -- @Note [Address offsets for shared libraries]@ in
    -- "Ambient.Loader.LoadOffset" for the details). However, we will want to
    -- support more flexible memory layouts such as ASLR in the future. In
    -- those sorts of layouts, we would run the risk of addresses from
    -- different address spaces being mapped to the same 'DMC.ArchSegmentOff',
    -- which will make a 'Map.Map' insufficient means of storage. See #86.
  , _simulationStats :: AmbientSimulationStats
    -- ^ Metrics from the Ambient simulator
  , _overrideLookupFunctionHandle :: Maybe (DMSMO.LookupFunctionHandle (AmbientSimulatorState sym arch) sym arch)
    -- ^ Override for the default 'DMSMO.LookupFunctionHandle' implementation
    -- in Ambient.Verifier.SymbolicExecution.  If set this will be used for
    -- resolving function calls instead of the default lookup function.
    -- The Weird Machine Executor uses this to replace the default function
    -- lookup with one that will disassemble the function address and use a
    -- more relaxed code discovery classifier to handle gadgets that may
    -- unbalance the stack (which prevents Macaw from detecting them properly).
  , _sharedMemoryState :: AMS.AmbientSharedMemoryState sym (DMC.ArchAddrWidth arch)
  -- ^ Manages shared memory allocated during simulation.
  , _macawLazySimulatorState :: DMS.MacawLazySimulatorState sym (DMC.ArchAddrWidth arch)
    -- ^ The state used in the lazy @macaw-symbolic@ memory model, on top of
    -- which @grease@ is built.
  }

-- | An initial value for 'AmbientSimulatorState'.
emptyAmbientSimulatorState :: AmbientSimulatorState sym arch
emptyAmbientSimulatorState = AmbientSimulatorState
  { _functionOvHandles = Map.empty
  , _functionAddrOvHandles = Map.empty
  , _syscallOvHandles = MapF.empty
  , _discoveredFunctionHandles = Map.empty
  , _simulationStats = emptyAmbientSimulationStats
  , _overrideLookupFunctionHandle = Nothing
  , _sharedMemoryState = AMS.emptyAmbientSharedMemoryState
  , _macawLazySimulatorState = DMS.emptyMacawLazySimulatorState
  }

instance (DMC.ArchAddrWidth arch ~ w) =>
         DMS.HasMacawLazySimulatorState
           (AmbientSimulatorState sym arch) sym w where
  macawLazySimulatorState = macawLazySimulatorState

functionOvHandles :: Lens' (AmbientSimulatorState sym arch)
                           (Map.Map WF.FunctionName (AF.FunctionOverrideHandle arch))
functionOvHandles = lens _functionOvHandles
                         (\s v -> s { _functionOvHandles = v })

functionAddrOvHandles :: Lens' (AmbientSimulatorState sym arch)
                               (Map.Map (AF.FunctionAddrLoc (DMC.ArchAddrWidth arch))
                                        (AF.FunctionOverrideHandle arch))
functionAddrOvHandles = lens _functionAddrOvHandles
                             (\s v -> s { _functionAddrOvHandles = v })

syscallOvHandles :: Lens' (AmbientSimulatorState sym arch)
                          (MapF.MapF ASy.SyscallNumRepr ASy.SyscallFnHandle)
syscallOvHandles = lens _syscallOvHandles
                        (\s v -> s { _syscallOvHandles = v })

discoveredFunctionHandles :: Lens' (AmbientSimulatorState sym arch)
                                   (Map.Map (DMC.ArchSegmentOff arch) (AF.FunctionOverrideHandle arch))
discoveredFunctionHandles = lens _discoveredFunctionHandles
                                 (\s v -> s { _discoveredFunctionHandles = v })

-- serverSocketFDs :: Lens' (AmbientSimulatorState sym arch)
--                        (Map.Map Integer (Some ASONT.ServerSocketInfo))
-- serverSocketFDs = lens _serverSocketFDs
--                        (\s v -> s { _serverSocketFDs = v })

simulationStats :: Lens' (AmbientSimulatorState sym arch) AmbientSimulationStats
simulationStats = lens _simulationStats (\s v -> s { _simulationStats = v })

macawLazySimulatorState :: Lens' (AmbientSimulatorState sym arch)
                                 (DMS.MacawLazySimulatorState sym (DMC.ArchAddrWidth arch))
macawLazySimulatorState = lens _macawLazySimulatorState (\s v -> s { _macawLazySimulatorState = v })

overrideLookupFunctionHandle
  :: Lens' (AmbientSimulatorState sym arch)
           (Maybe (DMSMO.LookupFunctionHandle (AmbientSimulatorState sym arch) sym arch))
overrideLookupFunctionHandle =
  lens _overrideLookupFunctionHandle
       (\s v -> s { _overrideLookupFunctionHandle = v })

sharedMemoryState
  :: Lens' (AmbientSimulatorState sym arch)
           (AMS.AmbientSharedMemoryState sym (DMC.ArchAddrWidth arch))
sharedMemoryState =
  lens _sharedMemoryState (\s v -> s { _sharedMemoryState = v })

-- {-
-- Note [Lazily registering overrides]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- During symbolic simulation, the verifier needs to register function handles for
-- any overrides that have not yet been used by the simulator. This is done in a
-- lazy fashion: before the verifier simulates a function, it will check to see
-- if it has previously registered. If so, just use the previously registered
-- function handle. If not, allocate a fresh handle for that function, register
-- it, then proceed. This lazy behavior is helpful for two reasons:

-- 1. In general, the verifier may not have discovered all of the functions it
--    needs prior to starting simulation. As a result, at least some lazy
--    registration will be required to handle functions that aren't discovered
--    until subsequent runs of the code discoverer.

-- 2. As a practical matter, it is difficult to ascertain the types of syscall
--    function handles until simulation begins. Lazy registration avoids this
--    issue, as one can wait until one is in the context of LookupSyscallHandle,
--    where the types are within reach.

-- We track registered overrides in AmbientSimulatorState, which is a custom
-- personality data type the verifier tracks during simulation. The
-- LookupFunctionHandle and LookupSyscallHandle interfaces pass through
-- CrucibleState, so if we need to register a newly discovered override, it is a
-- matter of updating the AmbientSimulatorState inside of the CrucibleState and
-- returning the new state.

-- Registered overrides for functions can be stored in a simple Map, as their
-- types are easy to ascertain ahead of time. Registered overrides for syscalls,
-- on the other hand, are stored in a MapF. Since their types are difficult to
-- know ahead of time (point (2) above), existentially closing over their types
-- avoids this problem.

-- Note [Incremental code discovery]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- The verifier will not perform code discovery unless it needs to, as:

-- 1. Code discovery is fairly expensive, and
-- 2. In large binaries, one typically only needs to discover a portion of the
--    functions available in the binary.

-- Because of this, the verifier will only discover one function at a time, and
-- only if the verifier needs to find an address that has not previously been
-- discovered before. This has a number of consequences for the design of the
-- verifier:

-- * Because code discovery requires knowing which address to discover, the
--   first thing the verifier must do is determine the address corresponding
--   to the distinguished entry point function so that its code can be discovered.
--   If the user manually specifies an address, this is no issue. If the user
--   tries to find a function with a particular name, such as `main` (see
--   Note [Entry Point] in A.Verifier), then this is somewhat more challenging,
--   since we do not know a priori where `main`'s address is. We could uncover
--   this information by performing code discovery on all functions in the binary,
--   but this would be prohibitively expensive.

--   Our solution is to look at the section headers of the binary, which offer a
--   much cheaper way to map each function name to its address. This information
--   is stored in A.Loader.BinaryConfig.bcMainBinarySymbolMap. Note that this
--   won't work if the binary is stripped, but that is to be expected—there is
--   no hope of discovering code in a stripped binary unless you know the exact
--   address at which to start.

-- * When looking up a function in the verifier, we want to avoid code discovery
--   if the function has a user-supplied override, as the override obviates the
--   need to discover the function's CFG. But overrides apply to function names,
--   whereas the verifier looks up functions by their addresses. In order to know
--   which function addresses have overrides, we need to look up the names for
--   each address. This mapping is contained in a LoadedBinaryPath's
--   lbpEntryPoints field. Again, this information is gleaned by inspecting each
--   binary's section headers.

-- * When the verifier encounters a PLT stub, it knows the name of the function it
--   should jump to. But how does it know which binary the function is defined in?
--   We solve this problem by, once again, looking at each binary's section
--   headers. In particular, the A.Loader.BinaryConfig.bcDynamicFuncSymbolMap
--   field maps the names of global, dynamic functions (which are the only
--   functions that PLT stubs could reasonably jump to) to their addresses. When
--   the verifier encounters a PLT stub without an override, it will use the
--   bcDynamicFuncSymbolMap to determine the address in another binary to jump
--   to and then proceed like normal.

-- * After a function has been discovered for the first time, its CFG handle is
--   stored in the discoveredFunctionHandles field of AmbientSimulatorState. That
--   way, subsequent lookups of the function need not re-perform code discovery.
--   This is very much in the same vein as Note [Lazily registering overrides].

-- Note [Special pointer region numbers]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- The verifier's currently has an extremely simplistic view of dynamically
-- allocated memory: every call to malloc creates a unique region number that is
-- separate from every other call to malloc. Moreover, malloc will always return
-- a non-zero region number, as the region 0 is reserved for raw bitvector values.
-- Comparing pointers with different region numbers, therefore, is usually a sign
-- that something is amiss, and macaw will treat these situations as undefined
-- behavior. (See, for instance, `doPtrEq` in `macaw-symbolic`.)

-- This approach is extremely simplistic, but it usually works quite well in
-- practice. Unfortunately, there are some corner cases where this breaks down.
-- In particular, there is code in the wild that attempts to compare the addresses
-- of different pointers. To illustrate the difficulty, we will use the following
-- C program example that iterates over a stack-allocated array (this will take a
-- bit of exposition, so bear with me):

--   int arr[ARR_LEN];
--   for (int i = 0; i < ARR_LEN; i++) {
--     arr[i] = 0;
--   }

-- An optimizing compiler can optimize away the intermediate `i` index value by
-- instead traversing the stack. Here is what that may look like as AArch32
-- psuedo-assembly, where `r1` is the address to the top of the stack and `r2`
-- is an address somewhere between `sp` (the stack pointer) and `r1`:

--   0x0: str     #0, [r2, #4]!
--   0x4: cmp     r1, r2
--   0x8: bne     0x0

-- Here is what happens in these three lines:

-- 0x0: Write `0x0` to the memory that `r2` points to, then increment `r2`'s
--      address by 4.
-- 0x4: Compare the addresses of `r1` and `r2`. The full semantics of the `cmp`
--      instruction are too complicated to describe here, but one key step is
--      that a value derived from `r1` and `r2` will be compared to `0x0`. If
--      they are equal, the Z condition flag will be set. Otherwise, Z will
--      not be set.
-- 0x8: If the Z condition flag is not set, then go back to address 0x0.
--      Otherwise, proceed.

-- This works because the compiler knows what part of the stack is dedicated to
-- storing `arr`'s elements, so the assembly iterates over the relevant stack
-- addresses rather than incrementing an intermediate variable. The loop will
-- end when `r1` and `r2` contain the same address, which will cause the Z
-- condition flag to be set.

-- OK, what does any of this have to do with allocation region numbers in the
-- verifier? Recall that raw bitvectors always have a region number of 0, whereas
-- malloc'd memory always has a non-zero region number. This is dire for the
-- example above, since `r1` and `r2` are both derived from `sp`. The verifier
-- backs the memory in the stack pointer with a chunk of malloc'd memory, which
-- means that `sp` (and any pointer resulting from arithmetic on `sp`) will have
-- a non-zero region number. As a result, the verifier will always claim that
-- `r1`/`r2` are not equal to 0x0, as they always have different region numbers.
-- This means that the Z flag will never be set, which will cause this loop to
-- never terminate. Ack!

-- The issue ultimately lies in the fact that the verifier's treatment of
-- dynamically allocated memory is not very well equipped to handle pointer
-- comparisons in general. The simplistic approach of giving every piece of
-- malloc'd memory a unique region number is good for catching undefined behavior,
-- but it is less suitable for handling the sorts of pointer optimizations seen
-- above. In the long term, we will want a more nuanced approach to dynamic
-- memory allocation.

-- In the short term, however, we get by with a hack: we treat the stack pointer's
-- region number specially. That is, we recognize that compilers are liable to do
-- stack-traversing optimizations like the one above that require more flexibility
-- vis-à-vis pointer comparisons. As a result, we override the following macaw
-- operations and provide slightly different semantics when one of the arguments
-- is a pointer with the same region number as the stack pointer:

-- * PtrEq: Normally, macaw's default behavior is to treat pointers from different
--   regions as being uncomparable. If one of the pointers is derived from the
--   stack pointer, however, we relax this requirement and simply compare the
--   pointer offsets without considering the region numbers.

-- * PtrToBits: Normally, macaw will only allow converting pointers with the region
--   number 0 to a raw bitvector. If the pointer is derived from the stack pointer,
--   however, we relax this requirement and simply convert the pointer offset to a
--   bitvector.

-- It is worth emphasizing that this is a hack. It is possible that there are other
-- special pointers requiring similar treatment that we have not yet identified.
-- If that is the case, we will need to expand the scope of the hack (i.e., the
-- `hasSpecialPointerBlock` function will need to be changed). It is also possible
-- that there are other macaw operations that need to be included above. For
-- instance, PtrToBits only applies to pointer comparisons where the pointer width
-- is the same as the architecture width. This appears to be enough in practice to
-- handle the type of code illustrated above, but this may not work if a pointer's
-- width is truncated or widened.

-- One might wonder: what happens if we apply this hack to /all/ pointers, not just
-- the stack pointer? While tempting, this would return incorrect behavior for C
-- programs that check if a pointer is NULL, which is a common idiom:

--   int *x = malloc(sizeof(int));
--   if (x != NULL) {
--     puts("This should be printed");
--   }

-- We know that each call to malloc returns a unique, non-zero region number. This
-- guarantees that the pointer representing `x`'s address is (1) not the same as
-- the stack pointer's region, and (2) not zero, which is the region number for
-- NULL (i.e., 0x0). In this particular example, we /do/ want to consider the
-- region number when checking for pointer equality, so it is important that we
-- exclude it from the scope of the hack.
-- -}
