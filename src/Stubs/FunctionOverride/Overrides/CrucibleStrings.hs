{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Overrides that involve Crucible 'LCT.StringType's. Note that these are not
-- suitable for calling from a binary, as there is no direct means to convert
-- registers to/from Crucible strings. Rather, these are meant to be called
-- from syntax overrides. To help enforce this convention, the names of these
-- overrides use hyphens (e.g., @read-c-string@), which prevents them from
-- being valid C identifiers. This isn't foolproof, of course, since an
-- especially determined user could find a way to create a binary in which
-- @read-c-string@ is a function symbol, but it does make the likelihood of
-- name collisions much, much less likely.
module Stubs.FunctionOverride.Overrides.CrucibleStrings
  ( crucibleStringOverrides
  , buildReadBytesOverride
  , callReadBytes
  , buildReadCStringOverride
  , callReadCString
  , buildWriteBytesOverride
  , callWriteBytes
  , buildWriteCStringOverride
  , callWriteCString
  , printPointerOverride
  , callPrintPointer
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Text as DT
import qualified Data.Text.Encoding as DTE
import qualified Data.Text.Encoding.Error as DTEE
import qualified Data.Vector as V

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Extensions as AExt
import           Stubs.FunctionOverride
import qualified Stubs.Memory as AM

-- | All of the Crucible string–related overrides, packaged up for your
-- convenience.
crucibleStringOverrides ::
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
crucibleStringOverrides initialMem unsupportedRelocs =
  [ SomeFunctionOverride (buildReadBytesOverride initialMem unsupportedRelocs)
  , SomeFunctionOverride (buildReadCStringOverride initialMem unsupportedRelocs)
  , SomeFunctionOverride (buildWriteBytesOverride initialMem)
  , SomeFunctionOverride (buildWriteCStringOverride initialMem)
  , SomeFunctionOverride printPointerOverride
  ]

buildReadBytesOverride ::
  ( LCLM.HasPtrWidth w
  , LCLM.HasLLVMAnn sym
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  AM.InitialMemory sym w ->
  Map.Map (DMC.MemWord w) String ->
  FunctionOverride (AExt.AmbientSimulatorState sym arch) sym
    (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) arch
    (LCT.VectorType (LCT.BVType 8))
buildReadBytesOverride initialMem unsupportedRelocs =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "read-bytes" $ \bak args ->
    Ctx.uncurryAssignment (callReadBytes bak initialMem unsupportedRelocs) args

-- | Override for the @read-bytes@ function. Note that:
-- * The loaded string must be concrete. If a symbolic character is encountered
--   while loading, this override will generate an assertion failure.
--
-- * The loaded string should be UTF-8–encoded. Any invalid code points in the
--   string will be replaced with the Unicode replacement character @U+FFFD@.
callReadBytes ::
  ( LCB.IsSymBackend sym bak
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , p ~ AExt.AmbientSimulatorState sym arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  AM.InitialMemory sym w ->
  Map.Map (DMC.MemWord w) String ->
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCT.VectorType (LCT.BVType 8)))
callReadBytes bak initialMem unsupportedRelocs ptr = do
  mem <- LCS.readGlobal $ AM.imMemVar initialMem
  symBytes <- AExt.loadString bak mem initialMem unsupportedRelocs ptr Nothing
  pure $ V.fromList symBytes

buildReadCStringOverride ::
  ( LCLM.HasPtrWidth w
  , LCLM.HasLLVMAnn sym
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  AM.InitialMemory sym w ->
  Map.Map (DMC.MemWord w) String ->
  FunctionOverride (AExt.AmbientSimulatorState sym arch) sym
    (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) arch
    (LCT.StringType WI.Unicode)
buildReadCStringOverride initialMem unsupportedRelocs =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "read-c-string" $ \bak args ->
    Ctx.uncurryAssignment (callReadCString bak initialMem unsupportedRelocs) args

-- | Override for the @read-c-string@ function. Note that the loaded bytes must
-- be concrete. If a symbolic byte is encountered while loading, this
-- override will generate an assertion failure.
callReadCString ::
  ( LCB.IsSymBackend sym bak
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , p ~ AExt.AmbientSimulatorState sym arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  AM.InitialMemory sym w ->
  Map.Map (DMC.MemWord w) String ->
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCT.StringType WI.Unicode))
callReadCString bak initialMem unsupportedRelocs ptr = do
  let sym = LCB.backendGetSym bak
  mem <- LCS.readGlobal $ AM.imMemVar initialMem
  bytes <- AExt.loadConcreteString bak mem initialMem unsupportedRelocs ptr Nothing
  let lit = DTE.decodeUtf8With DTEE.lenientDecode $ BS.pack bytes
  liftIO $ WI.stringLit sym $ WI.UnicodeLiteral lit

buildWriteBytesOverride ::
  ( LCLM.HasPtrWidth w
  , LCLM.HasLLVMAnn sym
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  AM.InitialMemory sym w ->
  FunctionOverride (AExt.AmbientSimulatorState sym arch) sym
    (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                  Ctx.::> LCT.VectorType (LCT.BVType 8)) arch
    LCT.UnitType
buildWriteBytesOverride initialMem =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "write-bytes" $ \bak args ->
    Ctx.uncurryAssignment (callWriteBytes bak initialMem) args

-- | Override for the @write-bytes@ function. Note that each byte provided as an
-- argument must be concrete. If given a symbolic string, this override will
-- generate an assertion failure.
callWriteBytes ::
  ( LCB.IsSymBackend sym bak
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , p ~ AExt.AmbientSimulatorState sym arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  AM.InitialMemory sym w ->
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  LCS.RegEntry sym (LCT.VectorType (LCT.BVType 8)) ->
  LCS.OverrideSim p sym ext r args ret ()
callWriteBytes bak initialMem ptr (LCS.regValue -> symBytes) = do
  let symBytesList = F.toList symBytes
  LCS.modifyGlobal (AM.imMemVar initialMem) $ \mem -> do
    mem' <- AExt.storeString bak mem initialMem ptr symBytesList
    pure ((), mem')

buildWriteCStringOverride ::
  ( LCLM.HasPtrWidth w
  , LCLM.HasLLVMAnn sym
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  AM.InitialMemory sym w ->
  FunctionOverride (AExt.AmbientSimulatorState sym arch) sym
    (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                  Ctx.::> LCT.StringType WI.Unicode) arch
    LCT.UnitType
buildWriteCStringOverride initialMem =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "write-c-string" $ \bak args ->
    Ctx.uncurryAssignment (callWriteCString bak initialMem) args

-- | Override for the @write-c-string@ function. Note that:
--
-- * The string argument must be concrete. If given a symbolic string, this
--   override will generate an assertion failure.
--
-- * The string will be UTF-8–encoded when written.
callWriteCString ::
  ( LCB.IsSymBackend sym bak
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , p ~ AExt.AmbientSimulatorState sym arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  AM.InitialMemory sym w ->
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  LCS.RegEntry sym (LCT.StringType WI.Unicode) ->
  LCS.OverrideSim p sym ext r args ret ()
callWriteCString bak initialMem ptr (LCS.regValue -> str) =
  LCS.modifyGlobal (AM.imMemVar initialMem) $ \mem ->
  case WI.asString str of
    Nothing -> LCS.overrideError $
      LCS.AssertFailureSimError "Call to @write-c-string with symbolic string" ""
    Just (WI.UnicodeLiteral txt) -> do
      -- Convert any escaped unicode characters into actual unicode
      let txt' = read ("\"" ++ DT.unpack txt ++ "\"") :: String

      -- Convert to bytes and write out
      let bytes = BS.unpack $ DTE.encodeUtf8 $ DT.pack txt'
      mem' <- AExt.storeConcreteString bak mem initialMem ptr bytes
      pure ((), mem')

-- | Override for the @print-pointer@ function.  Renders a pointer as a
-- crucible string using crucible's 'LCLM.ppPtr' function.
callPrintPointer
  :: ( LCB.IsSymInterface sym )
  => sym
  -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
  -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCT.StringType WI.Unicode))
callPrintPointer sym (LCS.regValue -> ptr) = do
  let ptrStr = show $ LCLM.ppPtr ptr
  liftIO $ WI.stringLit sym $ WI.UnicodeLiteral $ DT.pack ptrStr

printPointerOverride
  :: ( LCLM.HasPtrWidth w )
  => FunctionOverride (AExt.AmbientSimulatorState sym arch)
                      sym
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                      arch
                      (LCT.StringType WI.Unicode)
printPointerOverride =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "print-pointer" $ \bak args ->
    Ctx.uncurryAssignment (callPrintPointer (LCB.backendGetSym bak)) args
