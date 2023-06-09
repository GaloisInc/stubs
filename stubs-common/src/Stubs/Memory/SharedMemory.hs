-- | Functions and data types for managing shared memory state
module Stubs.Memory.SharedMemory
  ( AmbientSharedMemoryState
  , SharedMemoryId
  , asInteger
  , emptyAmbientSharedMemoryState
  , newSharedMemorySegment
  , sharedMemorySegmentAt
  ) where

import qualified Data.Map.Strict as Map

import qualified Lang.Crucible.LLVM.MemModel as LCLM

newtype SharedMemoryId = SharedMemoryId { asInteger :: Integer }
  deriving ( Eq, Ord, Show )

-- | Holds the state of shared memory.  This data type is meant to be opaque
-- and managed through the helper functions this module exports.
data AmbientSharedMemoryState sym w = AmbientSharedMemoryState
  { sharedMemoryNonce :: SharedMemoryId
  -- ^ A nonce for generated shared memory IDs
  , sharedMemorySegments :: Map.Map SharedMemoryId (LCLM.LLVMPtr sym w)
  -- ^ A mapping from shared memory IDs to allocations
  }

-- | The initial shared memory state
emptyAmbientSharedMemoryState :: AmbientSharedMemoryState sym w
emptyAmbientSharedMemoryState =
  AmbientSharedMemoryState { sharedMemoryNonce = SharedMemoryId 1
                           , sharedMemorySegments = Map.empty
                           }

-- | Given an ID and a shared memory state, get a pointer to the shared memory
-- segment at the ID (if any).
sharedMemorySegmentAt :: Integer
                      -> AmbientSharedMemoryState sym w
                      -> Maybe (LCLM.LLVMPtr sym w)
sharedMemorySegmentAt shmid shmState =
  Map.lookup (SharedMemoryId shmid) (sharedMemorySegments shmState)

-- | Given a pointer to a shared memory allocation and a shared memory state,
-- allocate a shared memory ID and insert the pointer into the shared memory
-- state.  Returns the segment's ID and an updated state.
newSharedMemorySegment :: LCLM.LLVMPtr sym w
                       -> AmbientSharedMemoryState sym w
                       -> (SharedMemoryId, AmbientSharedMemoryState sym w)
newSharedMemorySegment ptr shmState =
  let nonce = sharedMemoryNonce shmState
      SharedMemoryId nonceInt = nonce
      segments = sharedMemorySegments shmState in
  ( nonce
  , AmbientSharedMemoryState {
        sharedMemoryNonce = SharedMemoryId $ nonceInt + 1
      , sharedMemorySegments = Map.insert nonce ptr segments
      }
  )

