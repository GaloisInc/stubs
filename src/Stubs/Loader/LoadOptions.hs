module Stubs.Loader.LoadOptions
  ( indexToLoadOptions
  , addressToIndex
  , offsetAddressWithIndex
  ) where

import qualified Data.Bits as Bits
import           Data.Word ( Word64 )

import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.LoadCommon as MML

-- | Given an index value, constructs an 'MML.LoadOptions' for the appropriate
-- offset to load a shared object at.
-- See @Note [Address offsets for shared libraries]@.
indexToLoadOptions :: Word64 -> MML.LoadOptions
indexToLoadOptions index =
  MML.LoadOptions { MML.loadOffset = Just $ loadOffset * index }

-- | Given an address offset, determine the index of the binary that defines
-- the address. Examples:
--
-- @
-- 'addressToLoadOffset' 0x00001000 = 0
-- 'addressToLoadOffset' 0x10001000 = 1
-- 'addressToLoadOffset' 0x10001110 = 1
-- 'addressToLoadOffset' 0x20001110 = 2
-- @
--
-- See @Note [Address offsets for shared libraries]@.
addressToIndex :: DMM.MemWord w -> Integer
addressToIndex addr = DMM.memWordToUnsigned addr `Bits.shiftR` 28
  -- NB: 28 is equal to log_2(0x10000000), i.e., the number of binary
  -- digits we must shift past to uncover the high bits.

-- | Given an address, return an address that has been offset by the
-- appropriate amount. See @Note [Address offsets for shared libraries]@.
offsetAddressWithIndex :: DMM.MemWidth w => DMM.MemWord w -> Int -> DMM.MemWord w
offsetAddressWithIndex addr index = fromIntegral (loadOffset * index) + addr

-- | The address offset to use.
loadOffset :: Num a => a
loadOffset = 0x10000000

{-
Note [Address offsets for shared libraries]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When loading a binary with shared library dependencies, we must ensure that the
absoulte addresses for each binary do not clash with each other. We accomplish
this by using the following conventions for address offsets when loading
binaries:

* Addresses in the main binary are loaded as-is.
* For shared libraries lib_1, lib_2, ..., lib_n, the addresses in lib_i are
  offset by `0x10000000 * i`. (See `indexToLoadOptions`.)

When resolving address in `A.Verifier.SymbolicExecution.lookupFunction`, we
must also go in the opposite direction. That is, we must be able to take an
address with an already-applied offset and determine which binary it originally
came from. To do so:

* The `addressToIndex` function masks off the low bits in the address to
  determine the index of the binary. For instance, given the address
  0x20001000, its high bits are 2, indicating that the address comes from the
  second shared library. If the index is 0, then the address comes from the
  main binary.
* The `imBinaryMems` field in `InitialMemory` contains a vector of each
  binary's Memory at an index suitable for use with the indexing conventions
  established above. To retrieve the appropriate Memory for an address offset,
  use the value computed by `addressToIndex` as an index into `imBinaryMems`.

Be aware of the caveats to this approach to offsets:

* This load offset calculation is safe so long as all binaries are
  under 256MB.  It seems likely that something else in the verifier would
  fail before binaries reach that size.

* On 32-bit architectures, index values of 16 or higher will cause
  the offset to reach inaccessible values.  Macaw throws an exception in
  this case.  If this occurs in practice we will need to reduce the offset
  multiplier to something smaller (the trade-off is that the maximum
  allowable library size will also decrease).

* This approach requires some care regarding PLT stubs, as they add a layer of
  indirection between PLT function addresses, which reside in one binary, and
  the addresses that they ultimately jump to, which reside in a different
  binary. For this reason, PLT stubs are handled in a special case in
  `lookupFunction` that bypasses the indexing mechanisms described above.

* The commentary above describes one particular load strategy for shared
  objects. In the future, we will want to be able to configure the load
  strategy so that we can model things like ASLR. If we do this, we will need
  to update the code for resolving addresses accordingly. See #86.
-}
