{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- | This module defines utility functions for mapping argument types between
-- the macaw translation into crucible and the user-provided overrides in
-- crucible's concrete syntax.
--
-- This mapping enables users to specify that arguments should be bitvectors
-- using the native Crucible bitvector type.  Normally, the translation of macaw
-- into crucible requires that all bitvector-like arguments (bitvectors and
-- pointers) be of type LLVMPointer.  This is unintuitive for users, who do not
-- really need to understand why the macaw translation acts that way.  This
-- mapping code does the analysis to automatically convert types as necessary.
--
-- See Note [Bitvector Argument Mapping] for some additional details.
module Stubs.FunctionOverride.ArgumentMapping (
    bitvectorArgumentMapping
  , pointerArgumentMappping
  , buildFunctionOverrideArgs
  , buildForwardDecOverrideArgs
  , promoteBVToPtr
  , convertBitvector
  ) where

import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT

import qualified Stubs.Panic as AP

-- | Map user-provided override types to their corresponding types in the macaw
-- translation.
type family ToPointerType (tp :: LCT.CrucibleType) :: LCT.CrucibleType where
  ToPointerType (LCT.BVType w) = LCLM.LLVMPointerType w
  ToPointerType tp = tp

-- | Convert an 'Ctx.Assignment' of crucible types with bitvectors into an
-- 'Ctx.Assignment' of crucible types with only LLVMPointers.  The macaw
-- translation expects all bitvector-like values to be LLVMPointers, while some
-- of the user-specified overrides can mention bitvector arguments (for clarity
-- in the user-facing API).  This type family lets us convert user-specified
-- overrides into a form we can safely call.
type family CtxToPointerType (ctps :: Ctx.Ctx LCT.CrucibleType) :: Ctx.Ctx LCT.CrucibleType where
  CtxToPointerType Ctx.EmptyCtx = Ctx.EmptyCtx
  CtxToPointerType (tps Ctx.::> tp) = CtxToPointerType tps Ctx.::> ToPointerType tp

-- Promote any BV type in the user-provided override to an LLVMPointer, as
-- the translation from macaw to crucible assumes that all bitvector values
-- are of LLVMPointer type
--
-- Note that the only case that changes is the bitvector->LLVMPointer case
promoteBVToPtr
  :: LCT.TypeRepr tp
  -> LCT.TypeRepr (ToPointerType tp)
promoteBVToPtr ty =
  case ty of
    LCT.BVRepr w -> LCLM.LLVMPointerRepr w

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

-- | Maintain a mapping between argument types in the macaw translation and
-- user-specified overrides
--
-- The first 'LCT.TypeRepr' is the type of the actual argument passed from the caller (macaw translation).
--
-- The second 'LCT.TypeRepr' is the type expected by the user-provided override
data PointerArgumentMapping tp where
  PointerArgumentMapping :: LCT.TypeRepr (ToPointerType tp)
                         -> LCT.TypeRepr tp
                         -> PointerArgumentMapping tp

macawTranslationTypeRepr :: PointerArgumentMapping tp -> LCT.TypeRepr (ToPointerType tp)
macawTranslationTypeRepr (PointerArgumentMapping a _) = a

-- | A wrapper around a 'Ctx.Index' that existentially quantifies out the type
-- parameter (and where the exposed @tp@ is phantom).
--
-- This is used to map from indexes in one assignment into another.
data SomeIndex tps tp where
  SomeIndex :: Ctx.Index tps tp' -> SomeIndex tps tp

-- | A wrapper around a 'Ctx.Index' and 'LCT.TypeRepr' that we use to pair up an
-- index with its data payload value in assignments (see 'indexAssignment').
data IndexedType tps tp where
  IndexedType :: Ctx.Index tps tp -> LCT.TypeRepr tp -> IndexedType tps tp

-- | Pair up 'LCT.TypeRepr's with their 'Ctx.Index's; this is useful in direct
-- recursive traversals over assignments, as convenient combinators like
-- 'Ctx.generate' can't easily walk over two assignments with different "shapes"
-- in parallel.
indexAssignment :: Ctx.Assignment LCT.TypeRepr tps -> Ctx.Assignment (IndexedType tps) tps
indexAssignment as0 = Ctx.generate (Ctx.size as0) $ \idx -> IndexedType idx (as0 Ctx.! idx)


pointerArgumentMappping
  :: Ctx.Assignment PointerArgumentMapping tps
  -> ( Ctx.Assignment LCT.TypeRepr (CtxToPointerType tps)
     , Ctx.Assignment (SomeIndex (CtxToPointerType tps)) tps
     )
pointerArgumentMappping overrideTypes = (ptrTypes, revIdx)
  where
    ptrTypes = pointerArgumentTypes overrideTypes
    revIdx = pointerArgumentMappingRec (indexAssignment ptrTypes) overrideTypes

pointerArgumentMappingRec
  :: forall tps tps'
   . Ctx.Assignment (IndexedType tps') (CtxToPointerType tps)
  -> Ctx.Assignment PointerArgumentMapping tps
  -> Ctx.Assignment (SomeIndex tps') tps
pointerArgumentMappingRec ptrs overrides =
  case (ptrs, overrides) of
    (Ctx.Empty, Ctx.Empty) -> Ctx.Empty
    (ptrs' Ctx.:> IndexedType idx _rep, overrides' Ctx.:> _pam) ->
      pointerArgumentMappingRec ptrs' overrides' Ctx.:> SomeIndex idx

bitvectorArgumentMapping
  :: Ctx.Assignment LCT.TypeRepr tps
  -> Ctx.Assignment PointerArgumentMapping tps
bitvectorArgumentMapping tps =
  Ctx.generate (Ctx.size tps) $ \idx ->
    let tp = tps Ctx.! idx
    in PointerArgumentMapping (promoteBVToPtr tp) tp

pointerArgumentTypes
  :: Ctx.Assignment PointerArgumentMapping tps
  -> Ctx.Assignment LCT.TypeRepr (CtxToPointerType tps)
pointerArgumentTypes pam =
  case pam of
    Ctx.Empty -> Ctx.Empty
    rest Ctx.:> tp -> pointerArgumentTypes rest Ctx.:> macawTranslationTypeRepr tp

-- | Translate a single argument from its current type to the type expected by
-- the user-specified override.
convertBitvector
  :: (LCB.IsSymBackend sym bak)
  => bak
  -> LCT.TypeRepr tp
  -- ^ The type expected by the user-specified override
  -> LCS.RegEntry sym tp'
  -- ^ The value to convert
  -> IO (LCS.RegEntry sym tp)
convertBitvector bak to_tp re =
  case (LCS.regType re, to_tp) of
    (LCLM.LLVMPointerRepr w1, LCT.BVRepr w2)
      | Just PC.Refl <- PC.testEquality w1 w2 -> do
          bv <- LCLM.projectLLVM_bv bak (LCS.regValue re)
          return (LCS.RegEntry (LCT.BVRepr w1) bv)
    (LCT.BVRepr w1, LCLM.LLVMPointerRepr w2)
      | Just PC.Refl <- PC.testEquality w1 w2 -> do
          ptr <- LCLM.llvmPointer_bv sym (LCS.regValue re)
          return (LCS.RegEntry (LCLM.LLVMPointerRepr w1) ptr)
    (from_tp, _)
      | Just PC.Refl <- PC.testEquality to_tp from_tp -> return re
      | otherwise -> AP.panic AP.Override "buildFunctionOverrideArg" [ "Type mismatch in override arguments:"
                                                                     , " override expected: " ++ show to_tp
                                                                     , " actual argument type: " ++ show from_tp
                                                                     ]
  where
    sym = LCB.backendGetSym bak

-- | Given a 'PointerArgumentMapping' and a list of actual arguments
-- ('LCS.RegEntry') passed from crucible, convert the arguments that should be
-- bitvectors into plain bitvectors so that they can be passed to user
-- overrides.
buildFunctionOverrideArgs
  :: forall sym bak tps
   . (LCB.IsSymBackend sym bak)
  => bak
  -> Ctx.Assignment PointerArgumentMapping tps
  -> Ctx.Assignment (SomeIndex (CtxToPointerType tps)) tps
  -> Ctx.Assignment (LCS.RegEntry sym) (CtxToPointerType tps)
  -> IO (Ctx.Assignment (LCS.RegEntry sym) tps)
buildFunctionOverrideArgs bak pam argIdxs args =
  Ctx.generateM (Ctx.size pam) $ \idx ->
      case pam Ctx.! idx of
        PointerArgumentMapping _macawRepr overrideRepr -> do
          case argIdxs Ctx.! idx of
            SomeIndex argIdx -> convertBitvector bak overrideRepr (args Ctx.! argIdx)

-- | Given a list of arguments in an override for a forward declaration—see
-- @Note [Resolving forward declarations]@ in
-- "Stubs.FunctionOverride.Overrides.ForwardDeclarations"—convert any
-- bitvector arguments to pointers. This corresponds to step (1) in the Note.
buildForwardDecOverrideArgs ::
  forall sym bak tps.
  LCB.IsSymBackend sym bak =>
  bak ->
  Ctx.Assignment (LCS.RegEntry sym) tps ->
  IO (Ctx.Assignment (LCS.RegEntry sym) (CtxToPointerType tps))
buildForwardDecOverrideArgs bak = go
  where
    go :: forall tps'.
          Ctx.Assignment (LCS.RegEntry sym) tps' ->
          IO (Ctx.Assignment (LCS.RegEntry sym) (CtxToPointerType tps'))
    go Ctx.Empty         = pure Ctx.Empty
    go (rest Ctx.:> arg) = do
      rest' <- go rest
      arg'  <- convertBitvector bak (promoteBVToPtr (LCS.regType arg)) arg
      pure (rest' Ctx.:> arg')

{- Note [Bitvector Argument Mapping]

The high-level mapping problem is described above.  Because the macaw
translation passes all arguments as bitvectors, we need to translate the ones
that the user-specified overrides expect as bitvectors.  There is a simple
combinator for doing so (`projectLLVM_bv`), but we cannot just apply that to
every value of type LLVMPointer, as some must remain as pointers.

The major challenge in this code is maintaining the mapping from user override
expected types to macaw types.  Conceptually this is very easy: just map over
the user override types and promote the bitvectors to LLVMPointers.  However,
doing so in a type-safe way is tricky; we have:

- `Ctx.Assignment LCT.TypeRepr tps` for the user overrides
- `Ctx.Assignment LCT.TypeRepr (CtxToPointerType tps)` for the macaw caller

While these are "obviously" the same shape, since the latter is just the result
of mapping over the former, convincing GHC that they are the same is trickier.
To do it, we construct a parallel mapping of the two types (via
`PointerArgumentMapping`) and then construct a mapping between the indexes of
the two assignments in `pointerArgumentMapping`.  We then use that mapping in
`buildFunctionOverrideArgs` to convert the necessary parameters.

-}
