{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Stubs.FunctionOverride.StackArguments
  ( loadIntegerStackArgument
  ) where

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.Bytes as LCLB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

-- | Load integer arguments stored on the stack in preparation for a function
-- call. See @Note [Passing arguments to functions]@ in
-- "Ambient.FunctionOverride".
loadIntegerStackArgument ::
  forall sym bak arch w mem.
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , ?memOpts :: LCLM.MemOptions
  , DMS.SymArchConstraints arch
  , w ~ DMC.ArchAddrWidth arch
  , LCLM.HasPtrWidth w
  ) =>
  bak ->
  DMS.GenArchVals mem arch ->
  -- ^ Architecture information
  Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch) ->
  -- ^ A register structure containing symbolic values
  LCLM.MemImpl sym ->
  -- ^ The memory state at the time of the function call
  Int ->
  -- ^ Which argument should be read off of the stack? This is zero-indexed,
  -- so a value of @0@, @1@, @2@, etc. will read arguments located at offsets
  -- @0 * <ptr-width>@, @1 * <ptr-width>@, @2 * <ptr-width>@, etc. on the stack.
  --
  -- Some ABIs will put the first stack argument at offset 0, while other
  -- (e.g., x86_64) will put it after offset 0. Make sure that you are
  -- instantiating this argument with a value appropriate to the ABI.
  --
  -- This indexing scheme makes the assumption that all arguments have the
  -- same size, which isn't true in general. (See
  -- @Note [Passing arguments to functions]@, which discusses this limitation
  -- of our approach.) If we want to lift this restriction, we will need a more
  -- nuanced approach to calculating offsets that takes the type of the
  -- argument into consideration.
  IO (LCS.RegEntry sym (LCLM.LLVMPointerType w))
loadIntegerStackArgument bak archVals regs mem argIdx = do
  let ptrWidthBytes = LCLB.bitsToBytes $ WI.intValue ?ptrWidth
  off <- WI.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth
                                $ LCLB.bytesToInteger ptrWidthBytes * toInteger argIdx
  spOff <- LCLM.doPtrAddOffset bak mem (LCS.regValue stackPointer) off
  val <- LCLM.doLoad bak mem spOff (LCLM.bitvectorType ptrWidthBytes)
                     (LCLM.LLVMPointerRepr ?ptrWidth) LCLD.noAlignment
  pure $ LCS.RegEntry (LCLM.LLVMPointerRepr ?ptrWidth) val
  where
    sym = LCB.backendGetSym bak

    stackPointer = DMS.lookupReg archVals regsEntry DMC.sp_reg

    symArchFns :: DMS.MacawSymbolicArchFunctions arch
    symArchFns = DMS.archFunctions archVals

    crucRegTypes :: Ctx.Assignment LCT.TypeRepr (DMS.MacawCrucibleRegTypes arch)
    crucRegTypes = DMS.crucArchRegTypes symArchFns

    regsRepr :: LCT.TypeRepr (LCT.StructType (DMS.MacawCrucibleRegTypes arch))
    regsRepr = LCT.StructRepr crucRegTypes

    regsEntry :: LCS.RegEntry sym (LCT.StructType (DMS.MacawCrucibleRegTypes arch))
    regsEntry = LCS.RegEntry regsRepr regs
