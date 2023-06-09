{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Defines overrides and helper functions to support the printf family of
-- functions

module Stubs.FunctionOverride.Overrides.Printf
  ( printfFamilyOverrides
  , buildSprintfOverride
  , callSprintf
  , buildSscanfOverride
  , callSscanf
  ) where

import           Control.Applicative ( Alternative )
import           Control.Monad ( MonadPlus )
import           Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Control.Monad.State as CMS
import qualified Control.Monad.Trans as CMT
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.Char as C
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Traversable as T
import qualified Data.Vector as DV
import           Data.Void ( Void )
import           Data.Word ( Word8 )
import qualified GHC.Stack as GHC
import qualified Text.Megaparsec as TM
import qualified Text.Megaparsec.Byte as TMB
import qualified Text.Megaparsec.Byte.Lexer as TMBL

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.Bytes as LCLB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.Printf as LCLP
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.InterpretedFloatingPoint as WIFloat
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Extensions as AExt
import           Stubs.FunctionOverride
import qualified Stubs.Memory as AM
import qualified Stubs.MonadState as AMS
import           Stubs.Override

-- | All of the supported overrides in the @printf@ family of functions,
-- packaged up for your convenience.
printfFamilyOverrides ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  Map.Map (DMC.MemWord w) String ->
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  [SomeFunctionOverride (AExt.AmbientSimulatorState sym arch) sym arch]
printfFamilyOverrides initialMem unsupportedRelocs =
  [ SomeFunctionOverride (buildSprintfOverride initialMem unsupportedRelocs)
  , SomeFunctionOverride (buildSscanfOverride initialMem unsupportedRelocs)
  ]

-- | Override for the @sprintf@ function. This override has some limitations
-- on what arguments are allowed to be symbolic:
--
-- * The output string and the format string must be concrete, and the override
--   will add failing assertions if this is not the case. Other string arguments
--   are allowed to be symbolic.
--
-- * Arguments of any type besides string can be symbolic, but the override will
--   render them with @?@ characters. See ticket #118.
callSprintf
  :: forall sym bak w p ext r args ret arch scope st fs solver
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , DMC.MemWidth w
     , p ~ AExt.AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     , ?memOpts :: LCLM.MemOptions
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     )
  => bak
  -> AM.InitialMemory sym w
  -- ^ Initial memory state for symbolic execution
  -> Map.Map (DMC.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> Ctx.Assignment (LCS.RegEntry sym)
                    (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                  Ctx.::> LCLM.LLVMPointerType w)
  -- ^ The non-variadic arguments, consisting of (1) the output pointer, and
  -- (2) the format string
  -> GetVarArg sym
  -- ^ The variadic arguments
  -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callSprintf bak initialMem unsupportedRelocs
  (Ctx.Empty Ctx.:> outPtr Ctx.:> strPtr) gva = do
    let mvar = AM.imMemVar initialMem
    mem0 <- LCS.readGlobal mvar
    -- Read format string
    formatStr <- AExt.loadConcreteString bak mem0 initialMem unsupportedRelocs strPtr Nothing
    -- Parse format directives
    case LCLP.parseDirectives formatStr of
      Left err -> LCS.overrideError $
        LCS.AssertFailureSimError "Format string parsing failed" err
      Right ds -> do
        -- Compute output
        valist <- liftIO $ getPrintfVarArgs (DV.fromList ds) gva
        ((str, n), mem1) <-
          CMS.runStateT
            (executeDirectivesPrintf sym
                                     (printfOps bak initialMem unsupportedRelocs valist)
                                     ds)
            mem0

        -- Write to output pointer
        mem2 <- AExt.storeString bak mem1 initialMem outPtr str
        nBv <- liftIO $ WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth (toInteger n))
        LCS.writeGlobal mvar mem2
        liftIO $ bvToPtr sym nBv ?ptrWidth
  where
    sym = LCB.backendGetSym bak

buildSprintfOverride
  :: ( DMC.MemWidth w
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , p ~ AExt.AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     )

  => AM.InitialMemory sym w
  -- ^ Initial memory state for symbolic execution
  -> Map.Map (DMC.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                          Ctx.::> LCLM.LLVMPointerType w) arch
                            (LCLM.LLVMPointerType w)
buildSprintfOverride initialMem unsupportedRelocs =
  WI.withKnownNat ?ptrWidth $
  mkVariadicFunctionOverride "sprintf" $ \bak args getVarArg ->
    callSprintf bak initialMem unsupportedRelocs args getVarArg

-- | Override for the @sscanf@ function. This override has the following
-- limitations:
--
-- * Both the input string and the format string must be concrete.
--
-- * The input string is parsed in a very fast-and-loose way that largely
--   ignores things like modifiers. This is probably OK for most needs, as
--   we really only care that the correct value gets stored into memory. To put
--   it another way: this override does not faithfully implement the semantics
--   of the C @sscanf@ function.
callSscanf
  :: forall sym bak w p ext r args ret arch scope st fs solver
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , DMC.MemWidth w
     , p ~ AExt.AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     , ?memOpts :: LCLM.MemOptions
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     )
  => bak
  -> AM.InitialMemory sym w
  -- ^ Initial memory state for symbolic execution
  -> Map.Map (DMC.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> Ctx.Assignment (LCS.RegEntry sym)
                    (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                  Ctx.::> LCLM.LLVMPointerType w)
  -- ^ The non-variadic arguments, consisting of (1) the input pointer, and
  -- (2) the format string
  -> GetVarArg sym
  -- ^ The variadic arguments
  -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callSscanf bak initialMem unsupportedRelocs
  (Ctx.Empty Ctx.:> inPtr Ctx.:> strPtr) gva = do
    let mvar = AM.imMemVar initialMem
    mem0 <- LCS.readGlobal mvar
    -- Read format string
    formatStr <- AExt.loadConcreteString bak mem0 initialMem unsupportedRelocs strPtr Nothing
    -- Parse format directives
    case LCLP.parseDirectives formatStr of
      Left err -> LCS.overrideError $
        LCS.AssertFailureSimError "Format string parsing failed" err
      Right ds -> do
        -- Compute output
        valist <- liftIO $ getScanfVarArgs (DV.fromList ds) gva
        inStr <- AExt.loadConcreteString bak mem0 initialMem unsupportedRelocs inPtr Nothing
        (res, mem1) <-
          evalScanfOpsT mem0 (BS.pack inStr)
            (executeDirectivesScanf (scanfOps bak initialMem valist) ds)
        n <- case res of
               Left err -> LCS.overrideError $
                 LCS.AssertFailureSimError "sscanf input string parse error" $
                   TM.errorBundlePretty err
               Right n -> pure n

        LCS.writeGlobal mvar mem1
        nBv <- liftIO $ WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth (toInteger n))
        liftIO $ bvToPtr sym nBv ?ptrWidth
  where
    sym = LCB.backendGetSym bak

buildSscanfOverride
  :: ( DMC.MemWidth w
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , p ~ AExt.AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     )

  => AM.InitialMemory sym w
  -- ^ Initial memory state for symbolic execution
  -> Map.Map (DMC.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                          Ctx.::> LCLM.LLVMPointerType w) arch
                            (LCLM.LLVMPointerType w)
buildSscanfOverride initialMem unsupportedRelocs =
  WI.withKnownNat ?ptrWidth $
  mkVariadicFunctionOverride "sscanf" $ \bak args getVarArg ->
    callSscanf bak initialMem unsupportedRelocs args getVarArg

-- | Define handlers for the various printf directives.
--
-- NOTE: The only difference between this function and the version defined in
-- Crucible is that this function uses the Ambient-specific @loadString@
-- function.
printfOps :: ( LCB.IsSymBackend sym bak
             , LCLM.HasLLVMAnn sym
             , LCLM.HasPtrWidth w
             , DMC.MemWidth w
             , WPO.OnlineSolver solver
             , ?memOpts :: LCLM.MemOptions
             , sym ~ WE.ExprBuilder scope st fs
             , bak ~ LCBO.OnlineBackend solver scope st fs
             , p ~ AExt.AmbientSimulatorState sym arch
             , w ~ DMC.ArchAddrWidth arch
             )
          => bak
          -> AM.InitialMemory sym w
          -- ^ Initial memory state for symbolic execution
          -> Map.Map (DMC.MemWord w) String
          -- ^ Mapping from unsupported relocation addresses to the names of the
          -- unsupported relocation types.
          -> DV.Vector (LCS.AnyValue sym)
          -> PrintfOperations (CMS.StateT (LCLM.MemImpl sym) (LCS.OverrideSim p sym ext r args ret)) sym
printfOps bak initialMem unsupportedRelocs valist =
  let sym = LCB.backendGetSym bak in
  PrintfOperations
  { printfUnsupported = \x ->CMS.lift $ liftIO
                                      $ LCB.addFailedAssertion bak
                                      $ LCS.Unsupported GHC.callStack x

  , printfGetInteger = \i sgn _len ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue (LCLM.LLVMPointerRepr w) x) ->
         do bv <- liftIO (LCLM.projectLLVM_bv bak x)
            if sgn then
              return $ BVS.asSigned w <$> WI.asBV bv
            else
              return $ BVS.asUnsigned <$> WI.asBV bv
       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf"
                    (unwords ["Expected integer, but got:", show tpr])
       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                   "Out-of-bounds argument access in printf"
                   (unwords ["Index:", show i])

  , printfGetFloat = \i _len ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue (LCT.FloatRepr (_fi :: LCT.FloatInfoRepr fi)) x) ->
         do xr <- liftIO (WIFloat.iFloatToReal @_ @fi sym x)
            return (WI.asRational xr)
       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf."
                    (unwords ["Expected floating-point, but got:", show tpr])
       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Out-of-bounds argument access in printf:"
                    (unwords ["Index:", show i])

  , printfGetString  = \i numchars ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue LCLM.PtrRepr ptr) ->
           do mem <- CMS.get
              let reg = LCS.RegEntry (LCLM.LLVMPointerRepr ?ptrWidth) ptr
              CMS.lift $ AExt.loadString bak mem initialMem unsupportedRelocs reg numchars
       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf."
                    (unwords ["Expected char*, but got:", show tpr])
       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Out-of-bounds argument access in printf:"
                    (unwords ["Index:", show i])

  , printfGetPointer = \i ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue LCLM.PtrRepr ptr) ->
         return $ show (LCLM.ppPtr ptr)
       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf."
                    (unwords ["Expected void*, but got:", show tpr])
       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Out-of-bounds argument access in printf:"
                    (unwords ["Index:", show i])

  , printfSetInteger = \i len v ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue LCLM.PtrRepr ptr) ->
         do mem <- CMS.get
            case len of
              LCLP.Len_Byte  -> do
                 let w8 = WI.knownNat :: WI.NatRepr 8
                 let tp = LCLM.bitvectorType 1
                 x <- liftIO (LCLM.llvmPointer_bv sym =<< WI.bvLit sym w8 (BVS.mkBV w8 (toInteger v)))
                 mem' <- liftIO $ LCLM.doStore bak mem ptr (LCLM.LLVMPointerRepr w8) tp LCLD.noAlignment x
                 CMS.put mem'
              LCLP.Len_Short -> do
                 let w16 = WI.knownNat :: WI.NatRepr 16
                 let tp = LCLM.bitvectorType 2
                 x <- liftIO (LCLM.llvmPointer_bv sym =<< WI.bvLit sym w16 (BVS.mkBV w16 (toInteger v)))
                 mem' <- liftIO $ LCLM.doStore bak mem ptr (LCLM.LLVMPointerRepr w16) tp LCLD.noAlignment x
                 CMS.put mem'
              LCLP.Len_NoMod -> do
                 let w32  = WI.knownNat :: WI.NatRepr 32
                 let tp = LCLM.bitvectorType 4
                 x <- liftIO (LCLM.llvmPointer_bv sym =<< WI.bvLit sym w32 (BVS.mkBV w32 (toInteger v)))
                 mem' <- liftIO $ LCLM.doStore bak mem ptr (LCLM.LLVMPointerRepr w32) tp LCLD.noAlignment x
                 CMS.put mem'
              LCLP.Len_Long  -> do
                 let w64 = WI.knownNat :: WI.NatRepr 64
                 let tp = LCLM.bitvectorType 8
                 x <- liftIO (LCLM.llvmPointer_bv sym =<< WI.bvLit sym w64 (BVS.mkBV w64 (toInteger v)))
                 mem' <- liftIO $ LCLM.doStore bak mem ptr (LCLM.LLVMPointerRepr w64) tp LCLD.noAlignment x
                 CMS.put mem'
              _ ->
                CMS.lift $ liftIO
                         $ LCB.addFailedAssertion bak
                         $ LCS.Unsupported GHC.callStack
                         $ unwords ["Unsupported size modifier in %n conversion:", show len]

       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf."
                    (unwords ["Expected void*, but got:", show tpr])

       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Out-of-bounds argument access in printf:"
                    (unwords ["Index:", show i])
  }

-- | Like 'LCLP.PrintfOperations', but geared specifically towards the needs of
-- the @scanf@ family of functions.
data ScanfOperations m
  = ScanfOperations
    { scanfSetInteger  :: Int  -- Field number
                       -> Bool -- is Signed?
                       -> LCLP.PrintfLengthModifier
                       -> Integer
                       -> m ()
    , scanfSetFloat    :: Int -- FieldNumber
                       -> LCLP.PrintfLengthModifier
                       -> Rational
                       -> m ()
    , scanfSetPointer  :: Int -- FieldNumber
                       -> Integer
                       -> m ()
    , scanfSetString   :: Int -- FieldNumber
                       -> Maybe Int -- Number of chars to read; if Nothing, read until null terminator
                       -> [Word8]
                       -> m ()

    , scanfUnsupported :: !(forall a. GHC.HasCallStack => String -> m a)
    }

-- | Given a list of directives in a @scanf@ format string and a set of
-- 'ScanfOperations' to perform, parse the input string and perform the
-- appropriate operation for each directive. Note that the input string is not
-- an explicit input to this function; that is implicit in the 'String' part of
-- the @'TM.MonadParsec' 'Void' 'BS.ByteString'@ constraint.
--
-- If we wanted to more faithfully implement the semantics of the @scanf@
-- family of functions, we would need to pay more careful attention to things
-- like modifiers while parsing.
executeDirectivesScanf :: forall m. TM.MonadParsec Void BS.ByteString m
                       => ScanfOperations m
                       -> [LCLP.PrintfDirective]
                       -> m Int
executeDirectivesScanf ops directives = go 0 directives
  where
   go :: Int -> [LCLP.PrintfDirective] -> m Int
   go !_fld [] = do
     TM.eof
     pure (countConversionDirectives directives)
   go !fld (LCLP.StringDirective bs:xs) = do
       _ <- TMB.string bs
       go fld xs
   go !fld (LCLP.ConversionDirective d:xs) =
       let fld' = fromMaybe (fld+1) (LCLP.printfAccessField d) in
       case LCLP.printfType d of
         LCLP.Conversion_Integer fmt -> do
           let sgn = signedIntFormat fmt
           let intParser :: m Integer
               intParser = TMBL.signed (pure ()) TMBL.decimal
           i <- intParser
           scanfSetInteger ops fld' sgn (LCLP.printfLengthMod d) i
           go fld' xs
         LCLP.Conversion_Floating _fmt -> do
           let floatParser :: m Double
               floatParser = TMBL.signed (pure ()) TMBL.float
           f <- floatParser
           scanfSetFloat ops fld' (LCLP.printfLengthMod d) (toRational f)
           go fld' xs
         LCLP.Conversion_String -> do
           let strParser :: m BS.ByteString
               strParser = TM.takeWhileP (Just "%s") (not . C.isSpace . chr8)
           s <- strParser
           scanfSetString ops fld' (LCLP.printfPrecision d) (BS.unpack s)
           go fld' xs
         LCLP.Conversion_Char -> do
           let charParser :: m Word8
               charParser = TM.anySingle
           w8 <- charParser
           let sgn = False -- unsigned
           scanfSetInteger ops fld' sgn LCLP.Len_NoMod $ toInteger w8
           go fld' xs
         LCLP.Conversion_Pointer -> do
           let ptrParser :: m Integer
               ptrParser = TMB.char (ord8 '0') *> TMB.char (ord8 'x') *> TMBL.hexadecimal
           ptr <- ptrParser
           scanfSetPointer ops fld' ptr
           go fld' xs
         LCLP.Conversion_CountChars -> do
           let sgn = False -- unsigned
           len <- TM.getOffset
           scanfSetInteger ops fld' sgn (LCLP.printfLengthMod d) (toInteger len)
           go fld' xs

   -- Like 'C.chr', but for 'Word8' instead of 'Int'.
   chr8 :: Word8 -> Char
   chr8 = C.chr . fromIntegral

   -- Like 'C.ord', but for 'Word8' instead of 'Int'.
   ord8 :: Char -> Word8
   ord8 = fromIntegral . C.ord

-- | Copied from @crucible-llvm@, which is licensed under the 3-Clause BSD
-- license.
signedIntFormat :: LCLP.IntFormat -> Bool
signedIntFormat LCLP.IntFormat_SignedDecimal = True
signedIntFormat _ = False

-- | Count the number of 'LCLP.ConversionDirectives' in a format string. This
-- is precisely the value that the @scanf@ family of functions is meant to
-- return.
countConversionDirectives :: [LCLP.PrintfDirective] -> Int
countConversionDirectives = length . filter isConversionDirective
  where
    isConversionDirective :: LCLP.PrintfDirective -> Bool
    isConversionDirective LCLP.ConversionDirective{} = True
    isConversionDirective LCLP.StringDirective{}     = False

-- | An auxiliary monad transformer used in 'scanfOps'. This adds the following
-- effects on top of a monad @m@:
--
-- * A 'TM.ParsecT' effect for parsing a @scanf@ format string
--
-- * A 'CMS.StateT' effect for tracking symbolic memory state
newtype ScanfOpsT sym m a = ScanfOpsT
  (TM.ParsecT Void BS.ByteString (CMS.StateT (LCLM.MemImpl sym) m) a)
  deriving newtype ( Functor, Applicative, Monad
                   , Alternative, MonadPlus, MonadIO
                   , TM.MonadParsec Void BS.ByteString
                   , CMS.MonadState (LCLM.MemImpl sym)
                   )

instance CMT.MonadTrans (ScanfOpsT sym) where
  lift = ScanfOpsT . CMT.lift . CMT.lift

evalScanfOpsT ::
  Monad m =>
  LCLM.MemImpl sym ->
  BS.ByteString ->
  ScanfOpsT sym m a ->
  m (Either (TM.ParseErrorBundle BS.ByteString Void) a, LCLM.MemImpl sym)
evalScanfOpsT st mem (ScanfOpsT m) = CMS.runStateT (TM.runParserT m "" mem) st

-- | Define handlers for the various @scanf@ directives.
scanfOps ::
  forall m sym bak w arch p ext r args ret solver scope st fs.
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , WPO.OnlineSolver solver
  , ?memOpts :: LCLM.MemOptions
  , m ~ ScanfOpsT sym (LCS.OverrideSim p sym ext r args ret)
  , p ~ AExt.AmbientSimulatorState sym arch
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , w ~ DMC.ArchAddrWidth arch
  ) =>
  bak ->
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  DV.Vector (LCLM.LLVMPtr sym w) ->
  -- ^ Variadic arguments
  ScanfOperations m
scanfOps bak initialMem valist =
  ScanfOperations
  { scanfUnsupported = \x -> CMS.lift $ liftIO
                                      $ LCB.addFailedAssertion bak
                                      $ LCS.Unsupported GHC.callStack x

  , scanfSetInteger = \i _sgn _len int ->
      withArgIndex i $ \ptr -> do
        let tpr = LCLM.PtrRepr
        let ptrWidthBytes = LCLB.bitsToBytes $ WI.intValue ?ptrWidth
        let sty = LCLM.bitvectorType ptrWidthBytes
        intBV <- liftIO $ WI.bvLit sym ?ptrWidth $ BVS.mkBV ?ptrWidth int
        intPtr <- liftIO $ LCLM.llvmPointer_bv sym intBV
        store ptr tpr sty intPtr

  , scanfSetFloat = \i _len f ->
      withArgIndex i $ \ptr -> do
        let tpr = LCT.FloatRepr WIFloat.DoubleFloatRepr
        let sty = LCLM.doubleType
        d <- liftIO $ WIFloat.iFloatLitDouble sym $ fromRational f
        store ptr tpr sty d

  , scanfSetPointer = \i ptrVal ->
      withArgIndex i $ \ptr -> do
        let tpr = LCLM.PtrRepr
        let ptrWidthBytes = LCLB.bitsToBytes $ WI.intValue ?ptrWidth
        let sty = LCLM.bitvectorType ptrWidthBytes
        ptrValBV <- liftIO $ WI.bvLit sym ?ptrWidth $ BVS.mkBV ?ptrWidth ptrVal
        ptrValPtr <- liftIO $ LCLM.llvmPointer_bv sym ptrValBV
        store ptr tpr sty ptrValPtr

  , scanfSetString  = \i _numchars str ->
      withArgIndex i $ \ptr ->
      AMS.stateM $ \mem ->
        let ptrEntry = LCS.RegEntry LCLM.PtrRepr ptr in
        CMT.lift $ AExt.storeConcreteString bak mem initialMem ptrEntry str
  }
  where
    sym = LCB.backendGetSym bak

    withArgIndex ::
      Int ->
      (LCLM.LLVMPtr sym w -> m ()) ->
      m ()
    withArgIndex i k = do
      case valist DV.!? (i-1) of
        Just ptr -> k ptr
        Nothing ->
          liftIO $ LCB.addFailedAssertion bak
                 $ LCS.AssertFailureSimError
                  "Out-of-bounds argument access in scanf"
                  (unwords ["Index:", show i])

    store ::
      forall tp.
      LCLM.LLVMPtr sym w ->
      LCT.TypeRepr tp ->
      LCLM.StorageType ->
      LCS.RegValue sym tp ->
      m ()
    store ptr tpr sty val = AMS.stateM $ \mem -> do
      let ptrEntry = LCS.RegEntry LCLM.PtrRepr ptr
      szBV <- liftIO $ WI.bvLit sym ?ptrWidth $ BVS.mkBV ?ptrWidth $
              LCLB.bytesToInteger $ LCLM.storageTypeSize sty
      ptr' <- CMT.lift $ AMS.modifyM
        (liftIO . AExt.resolveAndPopulate bak mem initialMem szBV ptrEntry)
      liftIO $ LCLM.doStore bak mem ptr' tpr sty LCLD.noAlignment val

-- | Given the directives in a @printf@-style format string, retrieve the
-- corresponding variadic arguments. See @Note [Varargs]@ in
-- "Ambient.FunctionOverride" for a more detailed explanation of the mechanisms
-- at play.
getPrintfVarArgs ::
  forall sym w.
  LCLM.HasPtrWidth w =>
  DV.Vector LCLP.PrintfDirective ->
  GetVarArg sym ->
  IO (DV.Vector (LCS.AnyValue sym))
getPrintfVarArgs pds =
  CMS.evalStateT (DV.mapMaybeM (CMS.StateT . getPrintfVarArg) pds)

-- | Given a single directive in a @printf@-style format string:
--
-- * If it is a conversion directive (i.e., beginning with a @%@ character),
--   retrieve a variadic argument @arg@ of the corresponding type and return
--   @('Just' arg, gva)@, where @gva@ is the callback for retrieving the next
--   variadic argument. See @Note [Varargs]@ in "Ambient.FunctionOverride".
--
-- * Otherwise, return @('Nothing', gva)@.
getPrintfVarArg ::
  forall sym w.
  LCLM.HasPtrWidth w =>
  LCLP.PrintfDirective ->
  GetVarArg sym ->
  IO (Maybe (LCS.AnyValue sym), GetVarArg sym)
getPrintfVarArg pd gva@(GetVarArg getVarArg) =
  case pd of
    LCLP.StringDirective{} -> pure (Nothing, gva)
    LCLP.ConversionDirective cd ->
      case LCLP.printfType cd of
        LCLP.Conversion_Integer{}    -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_Char{}       -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_String{}     -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_Pointer{}    -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_CountChars{} -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_Floating{}   -> getArgWithType $ LCT.FloatRepr WIFloat.DoubleFloatRepr
  where
    getArgWithType ::
      forall arg.
      LCT.TypeRepr arg ->
      IO (Maybe (LCS.AnyValue sym), GetVarArg sym)
    getArgWithType tpRepr = do
      (LCS.RegEntry ty val, gva') <- getVarArg tpRepr
      pure (Just (LCS.AnyValue ty val), gva')

-- | Given the directives in a @scanf@-style format string, retrieve the
-- corresponding variadic arguments. See @Note [Varargs]@ in
-- "Ambient.FunctionOverride" for a more detailed explanation of the mechanisms
-- at play.
getScanfVarArgs ::
  forall sym w.
  LCLM.HasPtrWidth w =>
  DV.Vector LCLP.PrintfDirective ->
  GetVarArg sym ->
  IO (DV.Vector (LCLM.LLVMPtr sym w))
getScanfVarArgs pds =
  CMS.evalStateT (DV.mapMaybeM (CMS.StateT . getScanfVarArg) pds)

-- | Given a single directive in a @scanf@-style format string:
--
-- * If it is a conversion directive (i.e., beginning with a @%@ character),
--   retrieve a variadic argument @arg@ return @('Just' arg, gva)@, where @gva@
--   is the callback for retrieving the next variadic argument. See
--   @Note [Varargs]@ in "Ambient.FunctionOverride".
--
-- * Otherwise, return @('Nothing', gva)@.
getScanfVarArg ::
  forall sym w.
  LCLM.HasPtrWidth w =>
  LCLP.PrintfDirective ->
  GetVarArg sym ->
  IO (Maybe (LCLM.LLVMPtr sym w), GetVarArg sym)
getScanfVarArg pd gva@(GetVarArg getVarArg) =
  case pd of
    LCLP.StringDirective{} -> pure (Nothing, gva)
    LCLP.ConversionDirective{} -> do
      (LCS.RegEntry _ val, gva') <- getVarArg LCLM.PtrRepr
      pure (Just val, gva')

-- | A description of how to process the different types of arguments in the
-- @printf@ family of functions.
--
-- This is heavily based on 'Lang.Crucible.LLVM.Printf.PrintfOperations', but
-- with the following differences:
--
-- * This version has an additional @sym@ type parameter.
--
-- * The return types of 'printfGetString' is @m ['WI.SymBV' sym 8]@ rather than
--   @m ['Word8']@ to permit the possibility of symbolic string arguments.
data PrintfOperations m sym
  = PrintfOperations
    { printfGetInteger  :: Int  -- Field number
                        -> Bool -- is Signed?
                        -> LCLP.PrintfLengthModifier
                        -> m (Maybe Integer)
    , printfGetFloat    :: Int -- FieldNumber
                        -> LCLP.PrintfLengthModifier
                        -> m (Maybe Rational)
    , printfGetPointer  :: Int -- FieldNumber
                        -> m String
    , printfGetString   :: Int -- FieldNumber
                        -> Maybe Int -- Number of chars to read; if Nothing, read until null terminator
                        -> m [WI.SymBV sym 8]
    , printfSetInteger  :: Int -- FieldNumber
                        -> LCLP.PrintfLengthModifier
                        -> Int -- value to set
                        -> m ()

    , printfUnsupported :: !(forall a. GHC.HasCallStack => String -> m a)
    }

-- | Given a set of 'PrintfOperations' to perform and a list of directives in a
-- @printf@ format string, parse the input string and perform the appropriate
-- operation for each directive.  This function returns a bytestring containing
-- the rendered string and an int containing the number of bytes in the
-- rendered string.
--
-- This is heavily based on 'Lang.Crucible.LLVM.Printf.executeDirectives', but
-- with the following differences:
--
-- * This implementation treats the rendered string as a sequence of bytes,
--   while the Crucible implementation treats the string as UTF-8 encoded. This
--   distinction is important for us because interpreting exploit payloads as
--   UTF-8 encoded can break them.  See Crucible issue #1010
--   (https://github.com/GaloisInc/crucible/issues/1010) for more info.
--
-- * This implementation allows strings to be symbolic in the
--   'LCLP.Conversion_String' case, whereas the Crucible implementation requires
--   them to be concrete.
executeDirectivesPrintf :: forall m sym.
                         ( MonadIO m
                         , LCB.IsSymInterface sym
                         )
                        => sym
                        -> PrintfOperations m sym
                        -> [LCLP.PrintfDirective]
                        -> m ([WI.SymBV sym 8], Int)
executeDirectivesPrintf sym ops = go id 0 0
  where
    w8 = WI.knownNat @8

    go :: ([WI.SymBV sym 8] -> [WI.SymBV sym 8])
       -> Int
       -> Int
       -> [LCLP.PrintfDirective]
       -> m ([WI.SymBV sym 8], Int)
    go fstr !len !_fld [] = return (fstr [], len)
    go fstr !len !fld ((LCLP.StringDirective bs):xs) = do
        bs' <- liftIO $ T.for (BS.unpack bs) $ \byte ->
               WI.bvLit sym w8 $ BVS.mkBV w8 $ fromIntegral byte
        let len'  = len + BS.length bs
        let fstr' = fstr . (bs' ++)
        go fstr' len' fld xs
    go fstr !len !fld (LCLP.ConversionDirective d:xs) =
        let fld' = fromMaybe (fld+1) (LCLP.printfAccessField d) in
        case LCLP.printfType d of
          LCLP.Conversion_Integer fmt -> do
            let sgn = signedIntFormat fmt
            i <- printfGetInteger ops fld' sgn (LCLP.printfLengthMod d)
            let istr = LCLP.formatInteger i fmt (LCLP.printfMinWidth d) (LCLP.printfPrecision d) (LCLP.printfFlags d)
            istr' <- asciiStrToSymBVs istr
            let len'  = len + length istr'
            let fstr' = fstr . (istr' ++)
            go fstr' len' fld' xs
          LCLP.Conversion_Floating fmt -> do
            r <- printfGetFloat ops fld' (LCLP.printfLengthMod d)
            rstr <- case LCLP.formatRational r fmt
                            (LCLP.printfMinWidth d)
                            (LCLP.printfPrecision d)
                            (LCLP.printfFlags d) of
                      Left err -> printfUnsupported ops err
                      Right a -> return a
            rstr' <- asciiStrToSymBVs rstr
            let len'  = len + length rstr'
            let fstr' = fstr . (rstr' ++)
            go fstr' len' fld' xs
          LCLP.Conversion_String -> do
            s <- printfGetString ops fld' (LCLP.printfPrecision d)
            let len'  = len + length s
            let fstr' = fstr . (s ++)
            go fstr' len' fld' xs
          LCLP.Conversion_Char -> do
            let sgn  = False -- unsigned
            i <- printfGetInteger ops fld' sgn LCLP.Len_NoMod
            let c :: Word8 = maybe (fromIntegral (C.ord '?')) fromInteger i
            c' <- asciiCharToSymBV c
            let len'  = len + 1
            let fstr' = fstr . (c' :)
            go fstr' len' fld' xs
          LCLP.Conversion_Pointer -> do
            pstr <- printfGetPointer ops fld'
            pstr' <- asciiStrToSymBVs pstr
            let len'  = len + length pstr'
            let fstr' = fstr . (pstr' ++)
            go fstr' len' fld' xs
          LCLP.Conversion_CountChars -> do
            printfSetInteger ops fld' (LCLP.printfLengthMod d) len
            go fstr len fld' xs

    -- Note that this function will only work as expected if the string consists
    -- entirely of characters within the ASCII character set! (I believe this
    -- to be the case for each of these functions' call sites.)
    asciiStrToSymBVs :: String -> m [WI.SymBV sym 8]
    asciiStrToSymBVs = T.traverse (asciiCharToSymBV . fromIntegral . C.ord)

    asciiCharToSymBV :: Word8 -> m (WI.SymBV sym 8)
    asciiCharToSymBV = liftIO . WI.bvLit sym w8 . BVS.mkBV w8 . fromIntegral
