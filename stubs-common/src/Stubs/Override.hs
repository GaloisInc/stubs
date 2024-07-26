{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.Override
  ( buildArgumentAssignment
  , narrowPointerType
  , extendPointerType
  , adjustPointerSize
  , overrideMemOptions
  ) where

import qualified Control.Monad.Catch as CMC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import           GHC.TypeNats ( type (<=) )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Stubs.Exception as AE
import qualified Stubs.FunctionOverride as AF
import qualified Stubs.Panic as AP

-- | Given argument types and a list of potential argument values, return a
-- a pair consisting of (1) an 'Ctx.Assignment' of the argument values, possibly
-- narrowed to the appropriate types, and (2) a 'AF.GetVarArg' callback for
-- retrieving additional variadic arguments (see @Note [Varargs]@ in
-- "Ambient.FunctionOverride").
--
-- The contents of the list of potential arguments can vary depending on
-- whether this function is used for a system call or function call. For system
-- calls, this will be a finite list of solely register arguments. For function
-- calls, this list will be infinite, where the beginning of the list will
-- consist of register arguments and the remainder of the list will consist of
-- different stack offsets to read arguments from memory. Each entry in the
-- list is monadic because of the possible need to load a value from memory.
-- See @Note [Passing arguments to functions]@ in "Ambient.FunctionOverride".
buildArgumentAssignment
  :: forall w args sym
   . (1 <= w, LCB.IsSymInterface sym)
  => sym
  -> LCT.CtxRepr args
  -- ^ Types of arguments
  -> [IO (LCS.RegEntry sym (LCLM.LLVMPointerType w))]
  -- ^ List of potential argument values
  -> IO (Ctx.Assignment (LCS.RegEntry sym) args, AF.GetVarArg sym)
  -- ^ The argument values and a callback for retrieving variadic arguments
buildArgumentAssignment sym argTyps argEntries = do
  (knownArgs, variadicArgs) <- buildAssignment argTyps argEntries
  pure ( knownArgs
       , AF.GetVarArg $ \tp -> getVarArg tp variadicArgs
       )
  where
    -- Build an 'Ctx.Assignment' for the a subset of the arguments,
    -- returning a 'AF.GetVarArg' callback for retrieiving the leftover
    -- arguments.
    buildAssignment
      :: forall args'
       . LCT.CtxRepr args'
      -> [IO (LCS.RegEntry sym (LCLM.LLVMPointerType w))]
      -> IO ( Ctx.Assignment (LCS.RegEntry sym) args'
            , [IO (LCS.RegEntry sym (LCLM.LLVMPointerType w))]
            )
    buildAssignment typs args = do
      -- Split the arguments we want to build an Assignment for off from the
      -- other arguments proceeding.
      let (argsPrefix, argsLeftOver) = splitAt (Ctx.sizeInt (Ctx.size typs)) args
      -- Also make sure to reverse the arguments passed here to ensure that it
      -- matches the right-to-left processing when using 'Ctx.viewAssign'.
      argAssn <- go typs $ reverse argsPrefix
      pure (argAssn, argsLeftOver)

    -- Retrieve a single variadic argument from head the vararg list, and
    -- also return a new callback that uses the tail of the vararg list.
    -- (See Note [Varargs] in Ambient.FunctionOverride for what \"vararg list\"
    -- means in this context.)
    getVarArg ::
      forall tp.
      LCT.TypeRepr tp ->
      [IO (LCS.RegEntry sym (LCLM.LLVMPointerType w))] ->
      -- ^ The vararg list
      IO (LCS.RegEntry sym tp, AF.GetVarArg sym)
    getVarArg tp args = do
      (Ctx.Empty Ctx.:> argEntry, argsLeftOver) <-
        buildAssignment (Ctx.singleton tp) args
      pure (argEntry, AF.GetVarArg $ \tp' -> getVarArg tp' argsLeftOver)

    -- Loop through a subset of the arguments, narrowing each argument's
    -- type if necessary. Note that this function has an invariant that the
    -- list of potential arguments must be equal to the size of the
    -- 'LCT.CtxRepr'.
    go :: forall args'
        . LCT.CtxRepr args'
       -> [IO (LCS.RegEntry sym (LCLM.LLVMPointerType w))]
       -> IO (Ctx.Assignment (LCS.RegEntry sym) args')
    go typs args =
      case Ctx.viewAssign typs of
        Ctx.AssignEmpty -> return Ctx.empty
        Ctx.AssignExtend typs' trep ->
          case args of
            [] -> AP.panic AP.Override "buildArgumentAssignment"
                           [ "Invariant violated"
                           , "Override expects too many arguments"
                           ]
            mkArg : args' -> do
              arg <- mkArg
              arg' <- narrowPointerType sym trep arg
              rest <- go typs' args'
              return (rest Ctx.:> arg')

-- | Bitvector conversion from a wide width to a more narrow type.
newtype BvNarrowing sym w tp where
  BvNarrowing :: (LCS.RegEntry sym (LCLM.LLVMPointerType w) -> IO (LCS.RegEntry sym tp))
               -> BvNarrowing sym w tp

-- | Convert a @wideTp@ to a @narrowTp@. If both types are
-- 'LCLM.LLVMPointerType's, truncate the wider type to the narrow type.
-- Otherwise, require the types to be the same.
narrowPointerType ::
  forall sym wideTp narrowTp.
  LCB.IsSymInterface sym =>
  sym ->
  LCT.TypeRepr narrowTp ->
  LCS.RegEntry sym wideTp ->
  IO (LCS.RegEntry sym narrowTp)
narrowPointerType sym narrowTypeRepr wideEntry
  | LCLM.LLVMPointerRepr widePtrW <- LCS.regType wideEntry
  = case MapF.lookup narrowTypeRepr (conversions widePtrW) of
      Nothing -> CMC.throwM $ AE.FunctionTypeBvNarrowingError widePtrW
      Just (BvNarrowing toRegWidth) -> toRegWidth wideEntry

  | otherwise
  = case WI.testEquality (LCS.regType wideEntry) narrowTypeRepr of
      Just WI.Refl -> pure wideEntry
      Nothing -> CMC.throwM AE.FunctionTypeMismatch
  where
    -- Mapping of bitvector conversions to a narrow types. The wider-sized
    -- bitvector with width @widePtrW@ should always be the last element in the
    -- 'MapF.fromList' list to ensure that wide-width bitvectors do not undergo
    -- any conversion.
    conversions :: forall widePtrW.
                   (1 <= widePtrW) =>
                   PN.NatRepr widePtrW ->
                   MapF.MapF LCT.TypeRepr (BvNarrowing sym widePtrW)
    conversions widePtrW =
      MapF.fromList [ MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @8)) (BvNarrowing (bvTrunc (WI.knownNat @8)))
                    , MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @16)) (BvNarrowing (bvTrunc (WI.knownNat @16)))
                    , MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @32)) (BvNarrowing (bvTrunc (WI.knownNat @32)))
                    , MapF.Pair (LCLM.LLVMPointerRepr widePtrW) (BvNarrowing return)
                    ]

    -- Truncate a bitvector down to @narrowPtrW@ bits.
    bvTrunc :: forall widePtrW narrowPtrW
             . (1 <= widePtrW, 1 <= narrowPtrW)
            => PN.NatRepr narrowPtrW
            -> LCS.RegEntry sym (LCLM.LLVMPointerType widePtrW)
            -> IO (LCS.RegEntry sym (LCLM.LLVMPointerType narrowPtrW))
    bvTrunc bvW ptr = adjustPointerEntrySize sym ptr bvW

-- | Bitvector conversion from a narrow type to a wider width.
-- Like 'BvConversion', except with the argument and result types in the
-- function reversed.
newtype BvExtension sym w tp where
  BvExtension :: (LCS.RegEntry sym tp -> IO (LCS.RegEntry sym (LCLM.LLVMPointerType w)))
              -> BvExtension sym w tp

-- | Convert a @narrowTp@ to a @wideTp@. If both types are
-- 'LCLM.LLVMPointerType's, zero-extend the narrow type to the wider type.
-- Otherwise, require the types to be the same.
extendPointerType ::
  forall sym narrowTp wideTp.
  LCB.IsSymInterface sym =>
  sym ->
  LCT.TypeRepr wideTp ->
  LCS.RegEntry sym narrowTp ->
  IO (LCS.RegEntry sym wideTp)
extendPointerType sym wideTypeRepr narrowEntry
  | LCLM.LLVMPointerRepr widePtrW <- wideTypeRepr
  = case MapF.lookup narrowTypeRepr (conversions widePtrW) of
      Nothing -> CMC.throwM $ AE.FunctionTypeBvExtensionError widePtrW
      Just (BvExtension toRegWidth) -> toRegWidth narrowEntry

  | otherwise
  = case WI.testEquality narrowTypeRepr wideTypeRepr of
      Just WI.Refl -> pure narrowEntry
      Nothing -> CMC.throwM AE.FunctionTypeMismatch
  where
    narrowTypeRepr = LCS.regType narrowEntry

    -- Mapping of conversions from narrow-width bitvectors to the wider width.
    -- The wider-sized bitvector with width @widePtrW@ should always be the
    -- last element in the 'MapF.fromList' list to ensure that wide-width
    -- bitvectors do not undergo any conversion.
    conversions :: forall widePtrW.
                   (1 <= widePtrW) =>
                   PN.NatRepr widePtrW ->
                   MapF.MapF LCT.TypeRepr (BvExtension sym widePtrW)
    conversions widePtrW =
      MapF.fromList [ MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @8)) (BvExtension (bvZext widePtrW))
                    , MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @16)) (BvExtension (bvZext widePtrW))
                    , MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @32)) (BvExtension (bvZext widePtrW))
                    , MapF.Pair (LCLM.LLVMPointerRepr widePtrW) (BvExtension return)
                    ]

    -- Zero-extend a bitvector to @widePtrW@ bits.
    bvZext :: forall narrowPtrW widePtrW
             . (1 <= narrowPtrW, 1 <= widePtrW)
            => PN.NatRepr widePtrW
            -> LCS.RegEntry sym (LCLM.LLVMPointerType narrowPtrW)
            -> IO (LCS.RegEntry sym (LCLM.LLVMPointerType widePtrW))
    bvZext bvW ptr = adjustPointerEntrySize sym ptr bvW

-- | Zero-extend or truncate a @'WI.SymBV' sym srcW@ to be of size @dstW@.
adjustBvSize ::
  forall sym srcW dstW.
  ( LCB.IsSymInterface sym
  , 1 <= srcW
  , 1 <= dstW
  ) =>
  sym ->
  WI.SymBV sym srcW ->
  PN.NatRepr dstW ->
  IO (WI.SymBV sym dstW)
adjustBvSize sym bv dstW =
  case PN.compareNat srcW dstW of
    PN.NatEQ -> pure bv
    PN.NatLT _w -> WI.bvZext sym dstW bv
    PN.NatGT _w -> WI.bvTrunc sym dstW bv
  where
    srcW :: PN.NatRepr srcW
    srcW = case WI.exprType bv of
             WI.BaseBVRepr w -> w

-- | Zero-extend or truncate an @'LCLM.LLVMPtr' sym srcW@ to be of size @dstW@.
adjustPointerSize ::
  forall sym srcW dstW.
  ( LCB.IsSymInterface sym
  , 1 <= srcW
  , 1 <= dstW
  ) =>
  sym ->
  LCLM.LLVMPtr sym srcW ->
  PN.NatRepr dstW ->
  IO (LCLM.LLVMPtr sym dstW)
adjustPointerSize sym srcPtr dstW = do
  let LCLM.LLVMPointer srcBase srcOffset = srcPtr
  dstOffset <- adjustBvSize sym srcOffset dstW
  pure $ LCLM.LLVMPointer srcBase dstOffset

-- | Zero-extend or truncate an @'LCLM.LLVMPtr' sym srcW@ 'LCS.RegEntry' to be of
-- size @dstW@.
adjustPointerEntrySize ::
  forall sym srcW dstW.
  ( LCB.IsSymInterface sym
  , 1 <= srcW
  , 1 <= dstW
  ) =>
  sym ->
  LCS.RegEntry sym (LCLM.LLVMPointerType srcW) ->
  PN.NatRepr dstW ->
  IO (LCS.RegEntry sym (LCLM.LLVMPointerType dstW))
adjustPointerEntrySize sym ptrEntry dstW =
  LCS.RegEntry (LCLM.LLVMPointerRepr dstW) <$>
  adjustPointerSize sym (LCS.regValue ptrEntry) dstW

-- | The memory options used to configure the memory model for system call and
-- function overrides.
--
-- We use the most lax memory options possible, as machine code breaks many of
-- the C-level rules.
overrideMemOptions :: LCLM.MemOptions
overrideMemOptions = LCLM.laxPointerMemOptions
