{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.Extensions.Memory
  ( MemPtrTable(..)
  , SymbolicMemChunk(..)
  , combineSymbolicMemChunks
  , newMemPtrTable
  , mapRegionPointers
  , mkGlobalPointerValidityPred
  , readBytesAsRegValue
  ) where

import qualified Control.Exception as X
import           Control.Lens ( folded )
import           Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.IntervalMap.Interval as IMI
import qualified Data.IntervalMap.Strict as IM
import qualified Data.List.Split as Split
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Vector as PV
import qualified Data.Sequence as Seq
import           Text.Printf ( printf )
import           GHC.TypeNats ( KnownNat )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.Permissions as DMMP
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Memory as DMSM
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified What4.Interface as WI

import qualified Stubs.Panic as AP

-- | An index of all of the (statically) mapped memory in a program, suitable
-- for pointer translation. This is much like the @MemPtrTable@ in
-- @macaw-symbolic@, except that:
--
-- 1. This one doesn't have a @memRepr@, since it's not needed. (The
--    @MemPtrTable@ in @macaw-symbolic@ probably doesn't need one either, for
--    that matter.)
--
-- 2. This one separately stores the 'memPtrArray' that gets written into the
--    'memPtr', since we need to add additional assertions to the array as we
--    lazily initialize memory. See @Note [Lazy memory initialization]@@.
data MemPtrTable sym arch =
  MemPtrTable { memPtrTable :: IM.IntervalMap (DMM.MemWord (DMC.ArchAddrWidth arch)) (SymbolicMemChunk sym)
              -- ^ The ranges of (static) allocations that are mapped
              , memPtr :: LCLM.LLVMPtr sym (DMC.ArchAddrWidth arch)
              -- ^ The pointer to the allocation backing all of memory
              , memPtrArray :: WI.SymArray sym (Ctx.SingleCtx (WI.BaseBVType (DMC.ArchAddrWidth arch))) (WI.BaseBVType 8)
              -- ^ The SMT array mapping addresses to symbolic bytes
              }

-- | A discrete chunk of a memory segment within global memory. Memory is
-- lazily initialized one 'SymbolicMemChunk' at a time. See
-- @Note [Lazy memory initialization]@.
data SymbolicMemChunk sym = SymbolicMemChunk
  { smcBytes :: Seq.Seq (WI.SymBV sym 8)
    -- ^ A contiguous region of symbolic bytes backing global memory.
    --   The size of this region is no larger than 'chunkSize'. We represent
    --   this as a 'Seq.Seq' since we frequently need to append it to other
    --   regions (see 'combineSymbolicMemChunks').
  , smcMutability :: LCLM.Mutability
    -- ^ Whether the region of memory is mutable or immutable.
  }

-- | If two 'SymbolicMemChunk's have the same 'LCLM.Mutability', then return
-- @'Just' chunk@, where @chunk@ contains the two arguments' bytes concatenated
-- together. Otherwise, return 'Nothing'.
combineSymbolicMemChunks ::
  SymbolicMemChunk sym ->
  SymbolicMemChunk sym ->
  Maybe (SymbolicMemChunk sym)
combineSymbolicMemChunks
  (SymbolicMemChunk{smcBytes = bytes1, smcMutability = mutability1})
  (SymbolicMemChunk{smcBytes = bytes2, smcMutability = mutability2})
  | mutability1 == mutability2
  = Just $ SymbolicMemChunk
             { smcBytes = bytes1 <> bytes2
             , smcMutability = mutability1
             }
  | otherwise
  = Nothing

-- | Create a new 'MemPtrTable'. The type signature for this function is very
-- similar to that of 'DMS.newGlobalMemory' in @macaw-symbolic@, but unlike
-- that function, this one does not initialize the array backing the
-- 'MemPtrTable'. Instead, the initialization is deferred until simulation
-- begins. See @Note [Lazy memory initialization]@.
newMemPtrTable ::
    forall sym bak m t arch w
  . ( 16 WI.<= w
    , DMM.MemWidth w
    , KnownNat w
    , w ~ DMC.ArchAddrWidth arch
    , LCB.IsSymBackend sym bak
    , LCLM.HasLLVMAnn sym
    , MonadIO m
    , ?memOpts :: LCLM.MemOptions
    , Traversable t
    )
 => DMSM.GlobalMemoryHooks w
 -- ^ Hooks customizing the memory setup
 -> bak
 -- ^ The symbolic backend used to construct terms
 -> LCLD.EndianForm
 -- ^ The endianness of values in memory
 -> t (DMC.Memory w)
 -- ^ The macaw memories
 -> m (LCLM.MemImpl sym, MemPtrTable sym arch)
newMemPtrTable hooks bak endian mems = do
  let sym = LCB.backendGetSym bak
  let ?ptrWidth = DMC.memWidthNatRepr @w

  memImpl1 <- liftIO $ LCLM.emptyMem endian

  let allocName = WI.safeSymbol "globalMemoryBytes"
  symArray <- liftIO $ WI.freshConstant sym allocName WI.knownRepr
  sizeBV <- liftIO $ WI.maxUnsignedBV sym ?ptrWidth
  (ptr, memImpl2) <- liftIO $ LCLM.doMalloc bak LCLM.GlobalAlloc LCLM.Mutable
                         "Global memory for ambient-verifier"
                         memImpl1 sizeBV LCLD.noAlignment

  tbl <- liftIO $ mergedMemorySymbolicMemChunks bak hooks mems
  memImpl3 <- liftIO $ LCLM.doArrayStore bak memImpl2 ptr LCLD.noAlignment symArray sizeBV
  let memPtrTbl = MemPtrTable { memPtrTable = tbl
                              , memPtr = ptr
                              , memPtrArray = symArray
                              }
  pure (memImpl3, memPtrTbl)

-- | Construct an 'IM.IntervalMap' mapping regions of memory to their bytes,
-- representing as 'SymbolicMemChunk's. The regions of memory are split apart
-- to be in units no larger than 'chunkSize' bytes.
-- See @Note [Lazy memory initialization]@.
mergedMemorySymbolicMemChunks ::
  forall sym bak t w.
  ( LCB.IsSymBackend sym bak
  , DMM.MemWidth w
  , Traversable t
  ) =>
  bak ->
  DMSM.GlobalMemoryHooks w ->
  t (DMM.Memory w) ->
  IO (IM.IntervalMap (DMM.MemWord w) (SymbolicMemChunk sym))
mergedMemorySymbolicMemChunks bak hooks mems =
  fmap (IM.fromList . concat) $ traverse memorySymbolicMemChunks mems
  where
    sym = LCB.backendGetSym bak
    w8 = WI.knownNat @8

    memorySymbolicMemChunks ::
      DMM.Memory w ->
      IO [(IM.Interval (DMM.MemWord w), SymbolicMemChunk sym)]
    memorySymbolicMemChunks mem = concat <$>
      traverse (segmentSymbolicMemChunks mem) (DMM.memSegments mem)

    segmentSymbolicMemChunks ::
      DMM.Memory w ->
      DMM.MemSegment w ->
      IO [(IM.Interval (DMM.MemWord w), SymbolicMemChunk sym)]
    segmentSymbolicMemChunks mem seg = concat <$>
      traverse (\(addr, chunk) ->
                 do allBytes <- mkSymbolicMemChunkBytes mem seg addr chunk
                    let mut | DMMP.isReadonly (DMM.segmentFlags seg) = LCLM.Immutable
                            | otherwise                              = LCLM.Mutable
                    let absAddr =
                          case DMM.resolveRegionOff mem (DMM.addrBase addr) (DMM.addrOffset addr) of
                            Just addrOff -> DMM.segmentOffset seg + DMM.segoffOffset addrOff
                            Nothing -> AP.panic AP.Extensions "segmentSymbolicMemChunks"
                                         ["Failed to resolve function address: " ++ show addr]
                    let size = length allBytes
                    let interval = IM.IntervalCO absAddr (absAddr + fromIntegral size)
                    let intervalChunks = chunksOfInterval (fromIntegral chunkSize) interval
                    let smcChunks = map (\bytes -> SymbolicMemChunk
                                                     { smcBytes = Seq.fromList bytes
                                                     , smcMutability = mut
                                                     })
                                        (Split.chunksOf chunkSize allBytes)
                    -- The length of these two lists should be the same, as
                    -- @chunksOfInterval size@ should return a list of the same
                    -- size as @Split.chunksOf size@.
                    pure $ X.assert (length intervalChunks == length smcChunks)
                         $ zip intervalChunks smcChunks)
               (DMM.relativeSegmentContents [seg])

    -- NB: This is the same code as in this part of macaw-symbolic:
    -- https://github.com/GaloisInc/macaw/blob/ef0ece6a726217fe6231b9ddf523868e491e6ef0/symbolic/src/Data/Macaw/Symbolic/Memory.hs#L373-L378
    mkSymbolicMemChunkBytes ::
         DMM.Memory w
      -> DMM.MemSegment w
      -> DMM.MemAddr w
      -> DMM.MemChunk w
      -> IO [WI.SymBV sym 8]
    mkSymbolicMemChunkBytes mem seg addr memChunk =
      liftIO $ case memChunk of
        DMM.RelocationRegion reloc ->
          DMSM.populateRelocation hooks bak mem seg addr reloc
        DMM.BSSRegion sz ->
          replicate (fromIntegral sz) <$> WI.bvLit sym w8 (BV.zero w8)
        DMM.ByteRegion bytes ->
          traverse (WI.bvLit sym w8 . BV.word8) $ BS.unpack bytes

-- | The maximum size of a 'SymbolicMemChunk', which determines the granularity
-- at which the regions of memory in a 'memPtrTable' are chunked up.
-- See @Note [Lazy memory initialization]@.
--
-- Currently, `chunkSize` is 1024, which is a relatively small number
-- that is the right value to be properly aligned on most architectures.
chunkSize :: Int
chunkSize = 1024

-- | @'splitInterval' x i@ returns @'Just' (i1, i2)@ if @hi - lo@ is strictly
-- greater than @x@, where:
--
-- * @lo@ is @l@'s lower bound and @hi@ is @l@'s upper bound.
--
-- * @i1@ is the subinterval of @i@ starting from @i@'s lower bound and going up
--   to (but not including) @lo + x@.
--
-- * @i2@ is the subinterval of @i@ starting from @lo + x@ and going up to @hi@.
--
-- Otherwise, this returns 'Nothing'.
splitInterval :: (Integral a, Ord a) => a -> IMI.Interval a -> Maybe (IMI.Interval a, IMI.Interval a)
splitInterval x i
  | x <= 0
  = AP.panic AP.Extensions "splitInterval"
      [ "chunk size must be positive, got " ++ show (toInteger x) ]
  | x < (IMI.upperBound i - IMI.lowerBound i)
  = Just $ case i of
      IMI.OpenInterval   lo hi -> (IMI.OpenInterval lo (lo + x), IMI.IntervalCO     (lo + x) hi)
      IMI.ClosedInterval lo hi -> (IMI.IntervalCO   lo (lo + x), IMI.ClosedInterval (lo + x) hi)
      IMI.IntervalCO     lo hi -> (IMI.IntervalCO   lo (lo + x), IMI.IntervalCO     (lo + x) hi)
      IMI.IntervalOC     lo hi -> (IMI.OpenInterval lo (lo + x), IMI.ClosedInterval (lo + x) hi)
  | otherwise
  = Nothing

-- | Like the 'L.chunksOf' function, but over an 'IMI.Interval' instead of a
-- list.
chunksOfInterval :: (Integral a, Ord a) => a -> IMI.Interval a -> [IMI.Interval a]
chunksOfInterval x = go
  where
    go i = case splitInterval x i of
             Just (i1, i2) -> i1 : go i2
             Nothing       -> [i]

-- | Construct a translator for machine addresses into LLVM memory model pointers.
--
-- This translator is used by the symbolic simulator to resolve memory addresses.

-- NB: This is nearly identical to the function of the same name in
-- macaw-symbolic, the only difference being that we use a different
-- MemPtrTable data type.
mapRegionPointers :: ( DMM.MemWidth w
                     , 16 WI.<= w
                     , LCB.IsSymInterface sym
                     , LCLM.HasLLVMAnn sym
                     , ?memOpts :: LCLM.MemOptions
                     , DMC.ArchAddrWidth arch ~ w
                     )
                  => MemPtrTable sym arch
                  -> DMS.GlobalMap sym LCLM.Mem w
mapRegionPointers mpt = DMS.GlobalMap $ \bak mem regionNum offsetVal ->
  let sym = LCB.backendGetSym bak in
  case WI.asNat regionNum of
    Just 0 -> do
      let ?ptrWidth = WI.bvWidth offsetVal
      LCLM.doPtrAddOffset bak mem (memPtr mpt) offsetVal
    Just _ ->
      -- This is the case where the region number is concrete and non-zero,
      -- meaning that it is already an LLVM pointer
      --
      -- NOTE: This case is not possible because we only call this from
      -- 'tryGlobPtr', which handles this case separately
      return (LCLM.LLVMPointer regionNum offsetVal)
    Nothing -> do
      -- In this case, the region number is symbolic, so we need to be very
      -- careful to handle the possibility that it is zero (and thus must be
      -- conditionally mapped to one or all of our statically-allocated regions.
      --
      -- NOTE: We can avoid making a huge static mux over all regions: the
      -- low-level memory model code already handles building the mux tree as it
      -- walks backwards over all allocations that are live.
      --
      -- We just need to add one top-level mux:
      --
      -- > ite (blockid == 0) (translate base) (leave alone)
      let ?ptrWidth = WI.bvWidth offsetVal
      zeroNat <- WI.natLit sym 0
      isZeroRegion <- WI.natEq sym zeroNat regionNum
      -- The pointer mapped to global memory (if the region number is zero)
      globalPtr <- LCLM.doPtrAddOffset bak mem (memPtr mpt) offsetVal
      LCLM.muxLLVMPtr sym isZeroRegion globalPtr (LCLM.LLVMPointer regionNum offsetVal)

-- | Create a function that computes a validity predicate for an LLVMPointer
-- that may point to the static global memory region.
--
-- We represent all of the statically allocated storage in a binary in a single
-- LLVM array.  This array is sparse, meaning that large ranges of the address
-- space are not actually mapped.  Whenever we use a pointer into this memory
-- region, we want to assert that it is inside one of the mapped regions and
-- that it does not violate any mutability constraints.
--
-- The mapped regions are recorded in the MemPtrTable.
--
-- We need to be a little careful: if the BlockID of the pointer is definitely
-- zero, we make a direct assertion.  Otherwise, if the pointer is symbolic, we
-- have to conditionally assert the range validity.
--
-- Note that we pass in an indication of the use of the pointer: if the pointer
-- is used to write, it must only be within the writable portion of the address
-- space (which is also recorded in the MemPtrTable).  If the write is
-- conditional, we must additionally mix in the predicate.
--
-- This is intended as a reasonable implementation of the
-- 'MS.MkGlobalPointerValidityPred'.

-- NB: This is nearly identical to the function of the same name in
-- macaw-symbolic, the only difference being that we use a different
-- MemPtrTable data type.
mkGlobalPointerValidityPred :: forall sym w arch
                             . ( LCB.IsSymInterface sym
                               , DMM.MemWidth w
                               , w ~ DMC.ArchAddrWidth arch
                               )
                            => MemPtrTable sym arch
                            -> DMS.MkGlobalPointerValidityAssertion sym w
mkGlobalPointerValidityPred mpt = \sym puse mcond ptr -> do
  let w = DMM.memWidthNatRepr @w
  -- If this is a write, the pointer cannot be in an immutable range (so just
  -- return False for the predicate on that range).
  --
  -- Otherwise, the pointer is allowed to be between the lo/hi range
  let inMappedRange off (range, mut)
        | DMS.pointerUseTag puse == DMS.PointerWrite && mut == LCLM.Immutable = return (WI.falsePred sym)
        | otherwise =
          case range of
            IM.IntervalCO lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUle sym lobv off
              hib <- WI.bvUlt sym off hibv
              WI.andPred sym lob hib
            IM.ClosedInterval lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUle sym lobv off
              hib <- WI.bvUle sym off hibv
              WI.andPred sym lob hib
            IM.OpenInterval lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUlt sym lobv off
              hib <- WI.bvUlt sym off hibv
              WI.andPred sym lob hib
            IM.IntervalOC lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUlt sym lobv off
              hib <- WI.bvUle sym off hibv
              WI.andPred sym lob hib

  let mkPred off = do
        ps <- mapM (inMappedRange off) $ IM.toList $ fmap smcMutability $ memPtrTable mpt
        ps' <- WI.orOneOf sym (folded . id) ps
        -- Add the condition from a conditional write
        WI.itePred sym (maybe (WI.truePred sym) LCS.regValue mcond) ps' (WI.truePred sym)


  let ptrVal = LCS.regValue ptr
  let (ptrBase, ptrOff) = LCLM.llvmPointerView ptrVal
  case WI.asNat ptrBase of
    Just 0 -> do
      p <- mkPred ptrOff
      let msg = printf "%s outside of static memory range (known BlockID 0): %s" (show (DMS.pointerUseTag puse)) (show (WI.printSymExpr ptrOff))
      let loc = DMS.pointerUseLocation puse
      let assertion = LCB.LabeledPred p (LCS.SimError loc (LCS.GenericSimError msg))
      return (Just assertion)
    Just _ -> return Nothing
    Nothing -> do
      -- In this case, we don't know for sure if the block id is 0, but it could
      -- be (it is symbolic).  The assertion has to be conditioned on the equality.
      p <- mkPred ptrOff
      zeroNat <- WI.natLit sym 0
      isZeroBase <- WI.natEq sym zeroNat ptrBase
      p' <- WI.itePred sym isZeroBase p (WI.truePred sym)
      let msg = printf "%s outside of static memory range (unknown BlockID): %s" (show (DMS.pointerUseTag puse)) (show (WI.printSymExpr ptrOff))
      let loc = DMS.pointerUseLocation puse
      let assertion = LCB.LabeledPred p' (LCS.SimError loc (LCS.GenericSimError msg))
      return (Just assertion)

-- | @'readBytesAsRegValue' sym repr bytes@ reads symbolic bytes from @bytes@
-- and interprets it as a 'LCS.RegValue' of the appropriate type, which is
-- determined by @repr@.
--
-- This function checks that the length of @bytes@ is equal to
-- @'DMC.memReprBytes' repr@, throwing a panic if this is not the case.
readBytesAsRegValue ::
  LCB.IsSymInterface sym =>
  sym ->
  DMC.MemRepr ty ->
  [WI.SymBV sym 8] ->
  IO (LCS.RegValue sym (DMS.ToCrucibleType ty))
readBytesAsRegValue sym repr bytes =
  case repr of
    DMC.BVMemRepr byteWidth endianness -> do
      bytesV <- maybe (panic [ "Expected " ++ show byteWidth ++ " symbolic bytes,"
                             , "Received " ++ show (length bytes) ++ " bytes"
                             ]) pure $
                PV.fromList byteWidth bytes
      bytesBV <- readBytesAsBV sym endianness bytesV
      LCLM.llvmPointer_bv sym bytesBV
    DMC.FloatMemRepr {} ->
      panic ["Reading floating point values is not currently supported"]
    DMC.PackedVecMemRepr {} ->
      panic ["Reading packed vector values is not currently supported"]
  where
    panic = AP.panic AP.Extensions "readBytesAsRegValue"

-- | Read @numBytes@ worth of symbolic bytes and concatenate them into a single
-- 'WI.SymBV', respecting endianness. This is used to service concrete reads of
-- immutable global memory. See @Note [Lazy memory initialization]@.
readBytesAsBV
  :: forall sym numBytes
   . ( LCB.IsSymInterface sym
     , 1 WI.<= numBytes
     )
  => sym
  -> DMM.Endianness
  -> PV.Vector numBytes (WI.SymBV sym 8)
  -> IO (WI.SymBV sym (8 WI.* numBytes))
readBytesAsBV sym endianness = go
  where
    -- Iterate through the bytes one at a time, concatenating each byte along
    -- the way. The implementation of this function looks larger than it
    -- actually is due to needing to perform type-level Nat arithmetic to make
    -- things typecheck. The details of the type-level arithmetic were copied
    -- from PATE (https://github.com/GaloisInc/pate/blob/815d906243fef33993e340b8965567abe5bfcde0/src/Pate/Memory/MemTrace.hs#L1204-L1229),
    -- which is licensed under the 3-Clause BSD license.
    go :: forall bytesLeft
        . (1 WI.<= bytesLeft)
       => PV.Vector bytesLeft (WI.SymBV sym 8)
       -> IO (WI.SymBV sym (8 WI.* bytesLeft))
    go bytesV =
      let resWidth = PV.length bytesV in
      let (headByte, unconsRes) = PV.uncons bytesV in
      case WI.isZeroOrGT1 (WI.decNat resWidth) of
        -- We have only one byte left, so return it.
        Left WI.Refl -> do
          WI.Refl <- return $ zeroSubEq resWidth (WI.knownNat @1)
          pure headByte
        -- We have more than one byte left, so recurse.
        Right WI.LeqProof ->
          case unconsRes of
            -- If this were Left, that would mean that there would only be
            -- one byte left, which is impossible due to the assumptions above.
            -- That is, this case is unreachable. Thankfully, GHC's constraint
            -- solver is smart enough to realize this in conjunction with
            -- EmptyCase.
            Left x -> case x of {}
            Right tailV -> do
              let recByteWidth = WI.decNat resWidth
              tailBytes <- go tailV

              WI.Refl <- return $ WI.lemmaMul (WI.knownNat @8) resWidth
              WI.Refl <- return $ WI.mulComm (WI.knownNat @8) recByteWidth
              WI.Refl <- return $ WI.mulComm (WI.knownNat @8) resWidth
              WI.LeqProof <- return $ mulMono (WI.knownNat @8) recByteWidth
              concatBytes sym endianness headByte tailBytes

-- | Concat a byte onto a larger word, respecting endianness.
concatBytes
  :: ( LCB.IsSymInterface sym
     , 1 WI.<= w
     )
  => sym
  -> DMM.Endianness
  -> WI.SymBV sym 8
  -> WI.SymBV sym w
  -> IO (WI.SymBV sym (8 WI.+ w))
concatBytes sym endianness byte bytes =
  case endianness of
    DMM.BigEndian -> WI.bvConcat sym byte bytes
    DMM.LittleEndian -> do
      WI.Refl <- return $ WI.plusComm (WI.bvWidth byte) (WI.bvWidth bytes)
      WI.bvConcat sym bytes byte

-- Additional proof combinators

mulMono :: forall p q x w. (1 WI.<= x, 1 WI.<= w) => p x -> q w -> WI.LeqProof 1 (x WI.* w)
mulMono x w = WI.leqTrans (WI.LeqProof @1 @w) (WI.leqMulMono x w)

zeroSubEq :: forall p q w n. (n WI.<= w, 0 ~ (w WI.- n)) => p w -> q n -> w WI.:~: n
zeroSubEq w n
  | WI.Refl <- WI.minusPlusCancel w n
  = WI.Refl

{-
Note [Lazy memory initialization]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We back the global memory in a binary with an SMT array of symbolic bytes. One
issue with this approach is that initializing the elements of this array is
expensive. Despite our best efforts to optimize how SMT array initialization
takes places, filling in each byte of a large (i.e., several megabytes or more)
binary upfront is usually enough eat up all the RAM on your machine.

For this reason, we deliberately avoid populating the entire array upfront.
Instead, we initialize memory lazily. Here is a first approximation of how this
works:

* When the verifier starts, we create an empty SMT array to back global memory
  but do not initialize any of its elements. (See `newMemPtrTable` for how this
  is implemented.) We store this array in a MemPtrTable for later use.

* At the same time, we also store an IntervalMap in the MemPtrTable
  that maps the addresses in each memory segment to the corresponding bytes.
  (See the `SymbolicMemChunk` data type, which stores these bytes.)

* During simulation, if we attempt to access global memory, we first check
  to see if we have previously accessed the memory segment(s) corresponding to
  the addresses that were are accessing. If we haven't, we then initialize the
  bytes corresponding to those memory segments (and _only_ those memory
  segments) in the SMT array. We then record the fact that we have accessed
  these segments in the `populatedMemChunks` field of the
  `AmbientSimulatorState`.

* How do we determine which memory segments correspond to a particular read or
  write? If it is a concrete read or write, this is straightforward, as we need
  only look up a single address in the IntervalMap. If it is a symbolic read or
  write, then things are trickier, since it could potentially access different
  memory regions. To accommodate this, we construct an interval spanning all of
  the possible addresses that the read/write could access (see
  Ambient.Extensions.ptrOffsetInterval and retrieve all parts of the
  IntervalMap that intersect with the interval. This is costly, but it ensures
  that the approach is sound.

This approach ensures that we only pay the cost of memory initialization when
it is absolutely necessary. In order to make it less costly, we also implement
two important optimizations:

1. Even if the memory is only initialized one memory segment at a time, that
   can still be expensive if one accesses memory in a very large segment.
   What's more, one usually only needs to access a small portion of the
   large segment, but with the approach described above, you'd still have to pay
   the cost of initializing the entire segment.

   For this reason, we split up the memory addresses at an even finer
   granularity than just the memory segments when creating the IntervalMap.
   We go further and split up each segment into chunks of `chunkSize` bytes
   each. This way, most memory accesses will only require initializing small
   chunks of the array, even if they happen to reside within large memory
   segments.

   Currently, `chunkSize` is 1024, which is a relatively small number
   that is the right value to be properly aligned on most architectures.

2. While tracking the writable global memory in an SMT array is important in
   case the memory gets updated, there's really no need to track the
   read-only global memory in an SMT array. After all, read-only memory can
   never be updated, so we can determine what read-only memory will be by
   looking up the corresponding bytes in the IntervalMap, bypassing the SMT
   array completely.

   To determine which parts of memory are read-only, each `SymbolicMemChunk`
   tracks whether its bytes are mutable or immutable. When performing a memory
   read, if we can conclude that all of the memory to be read is immutable
   (i.e., read-only), then we can convert the symbolic bytes to a bitvector.
   (See `readBytesAsRegValue` for how this is implemented.)

   There are several criteria that must be met in order for this to be
   possible:

   * The read must be concrete.

   * The amount of bytes to be read must lie within a contiguous part of
     read-only memory.

   * There must be enough bytes within this part of memory to cover the number
     of bytes that must be read.

   If one of these critera are not met, we fall back on the SMT array approach.

At some point, we would like to upstream this work to macaw-symbolic, as
nothing here is specific to AMBIENT. See
https://github.com/GaloisInc/macaw/issues/282. Much of the code that implements
was copied from macaw-symbolic itself, which is licensed under the 3-Clause BSD
license.
-}
