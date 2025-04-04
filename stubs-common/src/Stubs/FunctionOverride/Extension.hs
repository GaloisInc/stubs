{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Stubs.FunctionOverride.Extension (
    TypeAlias(..)
  , TypeLookup(..)
  , ExtensionParser
  , SomeExtensionWrapper(..)
  , extensionParser
  , extensionTypeParser
  , CrucibleSyntaxOverrides(..)
  , emptyCrucibleSyntaxOverrides
  , OverrideMapParseError(..)
  , machineCodeParserHooks
  ) where

import           Control.Applicative ( Alternative(empty) )
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as DT
import qualified Data.Vector as DV
import           GHC.TypeNats ( KnownNat, type (<=) )
import           Numeric.Natural ( Natural )
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.CFG.Expr as LCE
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.Syntax.Monad as LCSM
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP

import           Stubs.FunctionOverride.Extension.Types


-- | A list of every type alias.
allTypeAliases :: [TypeAlias]
allTypeAliases = [minBound .. maxBound]

-- | Parser for type extensions to crucible syntax
extensionTypeParser
  :: (LCSM.MonadSyntax LCSA.Atomic m)
  => Map.Map LCSA.AtomName (Some LCT.TypeRepr)
  -- ^ A mapping from additional type names to the crucible types they
  -- represent
  -> m (Some LCT.TypeRepr)
extensionTypeParser types = do
  name <- LCSC.atomName
  case Map.lookup name types of
    Just someTypeRepr -> return someTypeRepr
    Nothing -> empty

-- | Check that a 'WI.NatRepr' containing a value in bits is a multiple of 8.
-- If so, pass the result of the value divided by 8 (i.e., as bytes) to the
-- continuation. Otherwise, return a default result.
bitsToBytes ::
  WI.NatRepr bits ->
  a ->
  -- ^ Default value to use if @bits@ is not a multiple of 8
  (forall bytes. ((8 WI.* bytes) ~ bits) => WI.NatRepr bytes -> a) ->
  -- ^ Continuation to invoke is @bits@ is a multiple of 8
  a
bitsToBytes bitsRep nonMultipleOf8 multipleOf8 =
  PN.withDivModNat bitsRep w8 $ \bytesRep modRep ->
    case PN.isZeroNat modRep of
      PN.NonZeroNat -> nonMultipleOf8
      PN.ZeroNat
        |  PN.Refl <- PN.mulComm bytesRep w8
        -> multipleOf8 bytesRep
  where
    w8 = PN.knownNat @8

-- | Perform a case analysis on the type argument to @pointer-read@ or
-- @pointer-write@. If the supplied type is not supported, return 'empty'.
-- This function packages factors out all of the grungy pattern-matching and
-- constraint wrangling that @pointer-read@ and @pointer-write@ share in
-- common.
withSupportedPointerReadWriteTypes ::
  Alternative f =>
  LCT.TypeRepr tp ->
  -- ^ The type argument
  (forall bits bytes.
     ( tp ~ LCT.BVType bits
     , (8 WI.* bytes) ~ bits
     , 1 <= bits
     , 1 <= bytes
     ) =>
     WI.NatRepr bits ->
     WI.NatRepr bytes ->
     f a) ->
  -- ^ Continuation to use if the argument is @'LCT.BVRepr (8 'WI.*' bytes)@
  -- (for some positive number @bytes@).
  (forall bits bytes.
     ( tp ~ LCLM.LLVMPointerType bits
     , (8 WI.* bytes) ~ bits
     , 1 <= bits
     , 1 <= bytes
     ) =>
     WI.NatRepr bits ->
     WI.NatRepr bytes ->
     f a) ->
  -- ^ Continuation to use if the argument is
  -- @'LCLM.LLVMPointerRepr (8 'WI.*' bytes)@ (for some positive number
  -- @bytes@).
  f a
withSupportedPointerReadWriteTypes tp bvK ptrK =
  case tp of
    LCT.BVRepr bits ->
      bitsToBytes bits empty $ \bytes ->
        case PN.isPosNat bytes of
          Nothing -> empty
          Just PN.LeqProof -> bvK bits bytes
    LCLM.LLVMPointerRepr bits ->
      bitsToBytes bits empty $ \bytes ->
        case PN.isPosNat bytes of
          Nothing -> empty
          Just PN.LeqProof -> ptrK bits bytes
    _ -> empty

-- | Parser for syntax extensions to crucible syntax
--
-- Note that the return value is a 'Pair.Pair', which seems a bit strange
-- because the 'LCT.TypeRepr' in the first of the pair is redundant (it can be
-- recovered by inspecting the 'LCCR.Atom'). The return value is set up this way
-- because the use site of the parser in crucible-syntax expects the 'Pair.Pair'
-- for all of the parsers that it attempts; returning the 'Pair.Pair' here
-- simplifies the use site.
extensionParser :: forall s m ext arch w
                 . ( ExtensionParser m ext s
                   , ext ~ DMS.MacawExt arch
                   , w ~ DMC.ArchAddrWidth arch
                   , 1 <= w
                   , KnownNat w
                   , DMM.MemWidth w
                   )
                => Map.Map LCSA.AtomName (SomeExtensionWrapper arch)
                -- ^ Mapping from names to syntax extensions
                -> LCSC.ParserHooks ext
                -- ^ ParserHooks for the desired syntax extension
                -> m (Some (LCCR.Atom s))
                -- ^ A pair containing a result type and an atom of that type
extensionParser wrappers hooks =
  let ?parserHooks = hooks in
  LCSM.depCons LCSC.atomName $ \name ->
    case name of
      LCSA.AtomName "pointer-read" -> do
        -- Pointer reads are a special case because we must parse the type of
        -- the value to read as well as the endianness of the read before
        -- parsing the additional arguments as Atoms.
        LCSM.depCons LCSC.isType $ \(Some tp) ->
          LCSM.depCons LCSC.atomName $ \endiannessName ->
            case endiannessFromAtomName endiannessName of
              Just endianness ->
                let readWrapper =
                      buildPointerReadWrapper tp endianness in
                go (SomeExtensionWrapper readWrapper)
              Nothing -> empty
      LCSA.AtomName "pointer-write" -> do
        -- Pointer writes are a special case because we must parse the type of
        -- the value to write out as well as the endianness of the write before
        -- parsing the additional arguments as Atoms.
        LCSM.depCons LCSC.isType $ \(Some tp) ->
          LCSM.depCons LCSC.atomName $ \endiannessName ->
            case endiannessFromAtomName endiannessName of
              Just endianness ->
                let writeWrapper =
                      buildPointerWriteWrapper tp endianness in
                go (SomeExtensionWrapper writeWrapper)
              Nothing -> empty
      LCSA.AtomName "bv-typed-literal" -> do
        -- Bitvector literals with a type argument are a special case.  We must
        -- parse the type argument separately before parsing the remaining
        -- argument as an Atom.
        LCSM.depCons LCSC.isType $ \(Some tp) ->
          case tp of
            LCT.BVRepr{} ->
              go (SomeExtensionWrapper (buildBvTypedLitWrapper tp))
            _ -> empty
      LCSA.AtomName "fresh-vec" -> do
        -- Generating fresh vectors are a special case. We must parse the
        -- name and length arguments separately due to their need to be
        -- concrete, and we must parse the type argument separately before we
        -- can know the return type.
        LCSM.depCons LCSC.string $ \nmPrefix ->
          LCSM.depCons LCSC.isType $ \(Some tp) ->
            LCSM.depCons LCSC.nat $ \len ->
            go (SomeExtensionWrapper (buildFreshVecWrapper nmPrefix tp len))
      _ ->
        case Map.lookup name wrappers of
          Nothing -> empty
          Just w -> go w
  where
    go :: (?parserHooks :: LCSC.ParserHooks ext)
       => SomeExtensionWrapper arch
       -> m (Some (LCCR.Atom s))
    go (SomeExtensionWrapper wrapper) = do
      loc <- LCSM.position
      -- Generate atoms for the arguments to this extension
      operandAtoms <- LCSC.operands (extArgTypes wrapper)
      -- Pass these atoms to the extension wrapper and return an atom for the
      -- resulting value
      atomVal <- extWrapper wrapper operandAtoms
      endAtom <- LCSC.freshAtom loc atomVal
      return (Some endAtom)

    -- Parse an 'LCSA.AtomName' representing an endianness into a
    -- 'Maybe DMM.Endianness'
    endiannessFromAtomName endianness =
      case endianness of
        LCSA.AtomName "le" -> Just DMM.LittleEndian
        LCSA.AtomName "be" -> Just DMM.BigEndian
        _ -> Nothing

-- | Wrap a statement extension binary operator
binop :: (KnownNat w, Monad m)
      => (  WI.NatRepr w
         -> lhsType
         -> rhsType
         -> LCCE.StmtExtension ext (LCCR.Atom s) tp )
      -- ^ Binary operator
      -> lhsType
      -- ^ Left-hand side operand
      -> rhsType
      -- ^ Right-hand side operand
      -> m (LCCR.AtomValue ext s tp)
binop op lhs rhs =
  return (LCCR.EvalExt (op WI.knownNat lhs rhs))


-- | Wrap a syntax extension binary operator, converting a bitvector in the
-- right-hand side position to an 'LLVMPointerType' before wrapping.
binopRhsBvToPtr :: ( ext ~ DMS.MacawExt arch
                   , ExtensionParser m ext s
                   , 1 <= w
                   , KnownNat w )
                => (  WI.NatRepr w
                   -> lhsType
                   -> LCCR.Atom s (LCLM.LLVMPointerType w)
                   -> LCCE.StmtExtension ext (LCCR.Atom s) tp)
                -- ^ Binary operator taking an 'LLVMPointerType' in the
                -- right-hand side position
                -> lhsType
                -- ^ Left-hand side operand
                -> LCCR.Atom s (LCT.BVType w)
                -- ^ Right-hand side operand as a bitvector to convert to an
                -- 'LLVMPointerType'
                -> m (LCCR.AtomValue ext s tp)
binopRhsBvToPtr op p1 p2 = do
  toPtrAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr WI.knownNat p2)))
  binop op p1 toPtrAtom

-- | Wrapper for the 'DMS.PtrAdd' syntax extension that enables users to add
-- integer offsets to pointers:
--
-- > pointer-add ptr offset
--
-- Note that the underlying macaw primitive allows the offset to be in either
-- position. This user-facing interface is more restrictive.
wrapPointerAdd
  :: ( 1 <= w
     , KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCT.BVType w)
                      (LCLM.LLVMPointerType w)
wrapPointerAdd = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-add"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> LCT.BVRepr LCT.knownNat
  , extWrapper = Ctx.uncurryAssignment (binopRhsBvToPtr DMS.PtrAdd) }

-- | Wrapper for the 'DMS.PtrSub' syntax extension that enables users to
-- subtract integer offsets from pointers:
--
-- > pointer-sub ptr offset
--
-- Note that the underlying macaw primitive allows the offset to be in either
-- position. This user-facing interface is more restrictive.
wrapPointerSub
  :: ( 1 <= w
     , KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCT.BVType w)
                      (LCLM.LLVMPointerType w)
wrapPointerSub = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-sub"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> LCT.BVRepr LCT.knownNat
  , extWrapper = Ctx.uncurryAssignment (binopRhsBvToPtr (DMS.PtrSub . DMM.addrWidthRepr)) }

-- | Compute the difference between two pointers in bytes using 'DMS.PtrSub'
pointerDiff :: ( w ~ DMC.ArchAddrWidth arch
               , ext ~ DMS.MacawExt arch
               , ExtensionParser m ext s
               , 1 <= w
               , KnownNat w
               , DMM.MemWidth w )
            => LCCR.Atom s (LCLM.LLVMPointerType w)
            -> LCCR.Atom s (LCLM.LLVMPointerType w)
            -> m (LCCR.AtomValue ext s (LCT.BVType w))
pointerDiff lhs rhs = do
  ptrRes <- binop (DMS.PtrSub . DMM.addrWidthRepr) lhs rhs
  ptrAtom <- LCSC.freshAtom WP.InternalPos ptrRes
  -- 'DMS.PtrSub' of two pointers produces a bitvector (LLVMPointer with region
  -- 0) so 'DMS.PtrToBits' is safe here.
  return (LCCR.EvalApp (LCE.ExtensionApp (DMS.PtrToBits LCT.knownNat ptrAtom)))

-- | Wrapper for the 'DMS.PtrSub' syntax extension that enables users to
-- subtract pointers from pointers:
--
-- > pointer-diff ptr1 ptr2
wrapPointerDiff
  :: ( w ~ DMC.ArchAddrWidth arch
     , 1 <= w
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w )
                      (LCT.BVType w)
wrapPointerDiff = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-diff"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , extWrapper = Ctx.uncurryAssignment pointerDiff }

-- | Wrapper for 'DMS.MacawNullPtr' to construct a null pointer.
--
-- > make-null
wrapMakeNull
  :: ( w ~ DMC.ArchAddrWidth arch
     , 1 <= w
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      Ctx.EmptyCtx
                      (LCLM.LLVMPointerType w)
wrapMakeNull = ExtensionWrapper
  { extName = LCSA.AtomName "make-null"
  , extArgTypes = Ctx.empty
  , extWrapper = \_ ->
      let nullptr = DMS.MacawNullPtr (DMC.addrWidthRepr WI.knownNat) in
      return (LCCR.EvalApp (LCE.ExtensionApp nullptr)) }

-- | Wrapper for the 'DMS.PtrEq' syntax extension that enables users to test
-- the equality of two pointers.
--
-- > pointer-eq ptr1 ptr2
wrapPointerEq
  :: ( 1 <= w
     , KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w)
                      LCT.BoolType
wrapPointerEq = ExtensionWrapper
 { extName = LCSA.AtomName "pointer-eq"
 , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                           Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
 , extWrapper = Ctx.uncurryAssignment (binop (DMS.PtrEq . DMM.addrWidthRepr)) }

-- | Wrapper for the 'DMS.MacawReadMem' syntax extension that enables users to
-- read through a pointer to retrieve data at the underlying memory location.
--
-- > pointer-read type endianness ptr
buildPointerReadWrapper
  :: ( 1 <= w
     , KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     )
  => LCT.TypeRepr tp
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                      tp
buildPointerReadWrapper tp endianness = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-read"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , extWrapper =Ctx.uncurryAssignment (pointerRead tp endianness)}

-- | Read through a pointer using 'DMS.MacawReadMem'.
pointerRead :: ( w ~ DMC.ArchAddrWidth arch
               , DMM.MemWidth w
               , KnownNat w
               , ExtensionParser m ext s
               , ext ~ DMS.MacawExt arch
               )
            => LCT.TypeRepr tp
            -> DMM.Endianness
            -> LCCR.Atom s (LCLM.LLVMPointerType w)
            -> m (LCCR.AtomValue ext s tp)
pointerRead tp endianness ptr =
  withSupportedPointerReadWriteTypes tp
    (\bits bytes -> do -- `Bitvector w` case
      let readInfo = DMC.BVMemRepr bytes endianness
      let readExt = DMS.MacawReadMem (DMC.addrWidthRepr WI.knownNat) readInfo ptr
      readAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalExt readExt)
      return (LCCR.EvalApp (LCE.ExtensionApp (DMS.PtrToBits bits readAtom))))
    (\_bits bytes -> do -- `Pointer` case
      let readInfo = DMC.BVMemRepr bytes endianness
      let readExt = DMS.MacawReadMem (DMC.addrWidthRepr WI.knownNat) readInfo ptr
      return (LCCR.EvalExt readExt))

-- | Wrapper for the 'DMS.MacawWriteMem' syntax extension that enables users to
-- write data through a pointer to the underlying memory location.
--
-- > pointer-write type endianness ptr (val :: type)
buildPointerWriteWrapper
  :: ( w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , KnownNat w
     , ext ~ DMS.MacawExt arch
     )
  => LCT.TypeRepr tp
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> tp)
                      LCT.UnitType
buildPointerWriteWrapper tp endianness = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-write"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> tp
  , extWrapper = Ctx.uncurryAssignment (pointerWrite tp endianness) }

-- | Read through a pointer using 'DMS.MacawWriteMem'.
pointerWrite :: ( w ~ DMC.ArchAddrWidth arch
                , DMM.MemWidth w
                , KnownNat w
                , ExtensionParser m ext s
                , ext ~ DMS.MacawExt arch
                )
              => LCT.TypeRepr tp
              -> DMM.Endianness
              -> LCCR.Atom s (LCLM.LLVMPointerType w)
              -> LCCR.Atom s tp
              -> m (LCCR.AtomValue ext s LCT.UnitType)
pointerWrite tp endianness ptr val =
  withSupportedPointerReadWriteTypes tp
    (\bits bytes -> do -- `Bitvector w` case
      toPtrAtom <- LCSC.freshAtom WP.InternalPos
        (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr bits val)))
      let writeInfo = DMC.BVMemRepr bytes endianness
      let writeExt = DMS.MacawWriteMem (DMC.addrWidthRepr WI.knownNat)
                                       writeInfo
                                       ptr
                                       toPtrAtom
      return (LCCR.EvalExt writeExt))
    (\_bits bytes -> do -- `Pointer` case
      let writeInfo = DMC.BVMemRepr bytes endianness
      let writeExt = DMS.MacawWriteMem (DMC.addrWidthRepr WI.knownNat)
                                       writeInfo
                                       ptr
                                       val
      return (LCCR.EvalExt writeExt))

-- | Wrapper for constructing bitvector literals matching the size of an
-- 'LCT.BVRepr'.  This enables users to instantiate literals with portable
-- types (such as SizeT).
--
-- > bv-typed-literal type integer
buildBvTypedLitWrapper
  :: LCT.TypeRepr (LCT.BVType w)
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCT.IntegerType)
                      (LCT.BVType w)
buildBvTypedLitWrapper tp = ExtensionWrapper
  { extName = LCSA.AtomName "bv-typed-literal"
  , extArgTypes = Ctx.empty Ctx.:> LCT.IntegerRepr
  , extWrapper = Ctx.uncurryAssignment (bvTypedLit tp)  }

-- | Create a bitvector literal matching the size of an 'LCT.BVRepr'
bvTypedLit :: forall s ext w m
           . ( ExtensionParser m ext s )
          => LCT.TypeRepr (LCT.BVType w)
          -> LCCR.Atom s LCT.IntegerType
          -> m (LCCR.AtomValue ext s (LCT.BVType w))
bvTypedLit (LCT.BVRepr w) val = return (LCCR.EvalApp (LCE.IntegerToBV w val))

-- | Wrapper for generating a vector of the given length, where each element is
-- a fresh constant of the supplied type whose name is derived from the given
-- string. This is a convenience for users who wish to quickly generate
-- symbolic data (e.g., for use with @write-bytes@).
--
-- > fresh-vec string type integer
buildFreshVecWrapper ::
     DT.Text
  -> LCT.TypeRepr tp
  -> Natural
  -> ExtensionWrapper arch
                      Ctx.EmptyCtx
                      (LCT.VectorType tp)
buildFreshVecWrapper nmPrefix tp len = ExtensionWrapper
  { extName = LCSA.AtomName "fresh-vec"
  , extArgTypes = Ctx.empty
  , extWrapper = \_ -> freshVec nmPrefix tp len }

-- | Generate a vector of the given length, where each element is a fresh
-- constant of the supplied type whose name is derived from the given string.
freshVec :: forall s ext tp m.
            ExtensionParser m ext s
         => DT.Text
         -> LCT.TypeRepr tp
         -> Natural
         -> m (LCCR.AtomValue ext s (LCT.VectorType tp))
freshVec nmPrefix tp len = do
  case tp of
    LCT.FloatRepr fi ->
      mkVec (LCCR.FreshFloat fi)
    LCT.NatRepr ->
      mkVec LCCR.FreshNat
    _ | LCT.AsBaseType bt <- LCT.asBaseType tp ->
          mkVec (LCCR.FreshConstant bt)
      | otherwise ->
          empty
  where
    -- Construct an expression that looks roughly like:
    --
    --   (vector <tp> (fresh <s>_0) ... (fresh <s>_<n-1>))
    --
    -- Where the implementation of `fresh` is determined by the first argument.
    mkVec :: (Maybe WI.SolverSymbol -> LCCR.AtomValue ext s tp)
          -> m (LCCR.AtomValue ext s (LCT.VectorType tp))
    mkVec mkFresh = do
      vec <- DV.generateM (fromIntegral len) $ \i ->
        LCSC.freshAtom WP.InternalPos $ mkFresh $ Just $ WI.safeSymbol $
        DT.unpack nmPrefix ++ "_" ++ show i
      pure $ LCCR.EvalApp $ LCE.VectorLit tp vec

-- | Syntax extension wrappers
extensionWrappers
  :: (w ~ DMC.ArchAddrWidth arch, 1 <= w, KnownNat w, DMC.MemWidth w)
  => Map.Map LCSA.AtomName (SomeExtensionWrapper arch)
extensionWrappers = Map.fromList
  [ (LCSA.AtomName "pointer-add", SomeExtensionWrapper wrapPointerAdd)
  , (LCSA.AtomName "pointer-diff", SomeExtensionWrapper wrapPointerDiff)
  , (LCSA.AtomName "pointer-sub", SomeExtensionWrapper wrapPointerSub)
  , (LCSA.AtomName "pointer-eq", SomeExtensionWrapper wrapPointerEq)
  , (LCSA.AtomName "make-null", SomeExtensionWrapper wrapMakeNull)
  ]

-- | All of the crucible syntax extensions to support machine code
machineCodeParserHooks
  :: forall w arch proxy
   . (w ~ DMC.ArchAddrWidth arch, 1 <= w, KnownNat w, DMC.MemWidth w)
  => proxy arch
  -> TypeLookup
  -- ^ A lookup function from a 'TypeAlias' to the underlying Crucible type
  -- it represents.
  -> LCSC.ParserHooks (DMS.MacawExt arch)
machineCodeParserHooks proxy typeLookup =
  let TypeLookup lookupFn = typeLookup
      types = Map.fromList [ (LCSA.AtomName (DT.pack (show t)), lookupFn t)
                           | t <- allTypeAliases ] in
  LCSC.ParserHooks (extensionTypeParser types)
                   (extensionParser extensionWrappers (machineCodeParserHooks proxy typeLookup))