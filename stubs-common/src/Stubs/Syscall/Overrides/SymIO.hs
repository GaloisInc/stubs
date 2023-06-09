{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Syscalls that make use of @crucible-symio@.
--
-- This contains cargo-culted versions of functions from @crucible-llvm@'s
-- "Lang.Crucible.LLVM.SymIO" module (licensed under the 3-Clause BSD license)
-- that have been tweaked to work with the verifier's memory model.
module Stubs.Syscall.Overrides.SymIO
  ( symIOOverrides
  , buildReadOverride
  , callRead
  , buildWriteOverride
  , callWrite
  , buildOpenOverride
  , callOpen
  , buildCloseOverride
  , callClose
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.SymIO as LCSym
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Extensions as AExt
import qualified Stubs.Memory as AM
import           Stubs.Override
import           Stubs.Syscall

-- | All of the symbolic IO–related overrides, packaged up for your
-- convenience.
symIOOverrides ::
  ( LCLM.HasLLVMAnn sym
     , LCLM.HasPtrWidth w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     ) =>
  LCLS.LLVMFileSystem w ->
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  Map.Map (DMC.MemWord w) String ->
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  [SomeSyscall (AExt.AmbientSimulatorState sym arch) sym ext]
symIOOverrides fs initialMem unsupportedRelocs =
  [ SomeSyscall (buildReadOverride fs memVar)
  , SomeSyscall (buildWriteOverride fs memVar)
  , SomeSyscall (buildOpenOverride fs initialMem unsupportedRelocs)
  , SomeSyscall (buildCloseOverride fs memVar)
  ]
  where
    memVar = AM.imMemVar initialMem

-- | Override for the read(2) system call
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- argument and return values.
callRead :: ( LCLM.HasLLVMAnn sym
            , LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            )
         => LCLS.LLVMFileSystem w
         -> LCS.GlobalVar LCLM.Mem
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ File descriptor to read from
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ Pointer to buffer to read into
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ Maximum number of bytes to read
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callRead fs memVar bak fd buf count = do
  let sym = LCB.backendGetSym bak
  -- Drop upper 32 bits from fd to create a 32 bit file descriptor
  fdReg <- liftIO $ ptrToBv32 bak ?ptrWidth fd

  -- Convert 'count' to a bitvector
  countBv <- liftIO $ LCLM.projectLLVM_bv bak (LCS.regValue count)
  let countReg = LCS.RegEntry (LCT.BVRepr ?ptrWidth) countBv

  -- Use llvm override for read
  resBv <- LCLS.callReadFileHandle bak memVar fs fdReg buf countReg

  liftIO $ LCLM.llvmPointer_bv sym resBv

-- | Given a filesystem and a memvar, construct an override for read(2)
buildReadOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> Syscall p
                             sym
                             (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w)
                             ext
                             (LCLM.LLVMPointerType w)
buildReadOverride fs memVar =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "read" $ \bak args ->
    Ctx.uncurryAssignment (callRead fs memVar bak) args


-- | Override for the write(2) system call
callWrite :: ( LCLM.HasLLVMAnn sym
             , LCB.IsSymBackend sym bak
             , LCLM.HasPtrWidth w
             )
          => LCLS.LLVMFileSystem w
          -> LCS.GlobalVar LCLM.Mem
          -> bak
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -- ^ File descriptor to write to
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -- ^ Pointer to buffer to read from
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -- ^ Number of bytes to write
          -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callWrite fs memVar bak fd buf count = do
  let sym = LCB.backendGetSym bak
  let ?memOpts = overrideMemOptions
  -- Drop upper 32 bits from fd to create a 32 bit file descriptor
  fdReg <- liftIO $ ptrToBv32 bak ?ptrWidth fd

  -- Convert 'count' to a bitvector
  countBv <- liftIO $ LCLM.projectLLVM_bv bak (LCS.regValue count)
  let countReg = LCS.RegEntry (LCT.BVRepr ?ptrWidth) countBv

  -- Use the llvm override for write
  resBv <- LCLS.callWriteFileHandle bak memVar fs fdReg buf countReg

  liftIO $ LCLM.llvmPointer_bv sym resBv

buildWriteOverride :: ( LCLM.HasLLVMAnn sym
                      , LCLM.HasPtrWidth w
                      )
                   => LCLS.LLVMFileSystem w
                   -> LCS.GlobalVar LCLM.Mem
                   -> Syscall p
                             sym
                             (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w)
                             ext
                             (LCLM.LLVMPointerType w)
buildWriteOverride fs memVar =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "write" $ \bak args ->
    Ctx.uncurryAssignment (callWrite fs memVar bak) args

-- | This is identical to @crucible-llvm@'s 'LCLS.callOpenFile' function,
-- except that its internals use the verifier's 'AExt.loadString' function
-- instead of @crucible-llvm@'s own 'LCLM.loadString' function.
callOpenFile ::
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , p ~ AExt.AmbientSimulatorState sym arch
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  Map.Map (DMC.MemWord w) String ->
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  LCLS.LLVMFileSystem w ->
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  LCS.RegEntry sym (LCT.BVType 32) ->
  LCS.OverrideSim p sym ext rtp args ret (LCS.RegValue sym (LCT.BVType 32))
callOpenFile bak initialMem unsupportedRelocs fsVars filename_ptr _flags =
  do fileIdent <- loadFileIdent bak initialMem unsupportedRelocs filename_ptr
     LCSym.openFile (LCLS.llvmFileSystem fsVars) fileIdent $ \case
       Left LCSym.FileNotFound -> returnIOError32
       Right fileHandle -> LCLS.allocateFileDescriptor fsVars fileHandle

-- | Override for the open(2) system call
callOpen :: ( LCLM.HasLLVMAnn sym
            , LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            , sym ~ WE.ExprBuilder scope st fs
            , bak ~ LCBO.OnlineBackend solver scope st fs
            , p ~ AExt.AmbientSimulatorState sym arch
            , DMC.MemWidth w
            , w ~ DMC.ArchAddrWidth arch
            , WPO.OnlineSolver solver
            )
         => LCLS.LLVMFileSystem w
         -> AM.InitialMemory sym w
         -- ^ Initial memory state for symbolic execution
         -> Map.Map (DMC.MemWord w) String
         -- ^ Mapping from unsupported relocation addresses to the names of the
         -- unsupported relocation types.
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ File path to open
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ Flags to use when opening file
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callOpen fs initialMem unsupportedRelocs bak pathname flags = do
  let sym = LCB.backendGetSym bak
  let ?memOpts = overrideMemOptions
  -- Drop upper 32 bits from flags to create a 32 bit flags int
  flagsInt <- liftIO $ ptrToBv32 bak ?ptrWidth flags

  -- Use llvm override for open
  resBv <- callOpenFile bak initialMem unsupportedRelocs fs pathname flagsInt

  -- Pad result out to 64 bit pointer
  liftIO $ bvToPtr sym resBv ?ptrWidth

buildOpenOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     , p ~ AExt.AmbientSimulatorState sym arch
                     , DMC.MemWidth w
                     , w ~ DMC.ArchAddrWidth arch
                     )
                  => LCLS.LLVMFileSystem w
                  -> AM.InitialMemory sym w
                  -- ^ Initial memory state for symbolic execution
                  -> Map.Map (DMC.MemWord w) String
                  -- ^ Mapping from unsupported relocation addresses to the names of the
                  -- unsupported relocation types.
                  -> Syscall p
                            sym
                            (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                          Ctx.::> LCLM.LLVMPointerType w)
                            ext
                            (LCLM.LLVMPointerType w)
buildOpenOverride fs initialMem unsupportedRelocs =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "open" $ \bak args ->
    Ctx.uncurryAssignment (callOpen fs initialMem unsupportedRelocs bak) args

-- | Override for the write(2) system call
callClose :: ( LCLM.HasLLVMAnn sym
             , LCB.IsSymBackend sym bak
             , LCLM.HasPtrWidth w
             )
          => LCLS.LLVMFileSystem w
          -> LCS.GlobalVar LCLM.Mem
          -> bak
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -- ^ File descriptor to close
          -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callClose fs memVar bak fd = do
  let sym = LCB.backendGetSym bak
  let ?memOpts = overrideMemOptions
  -- Drop upper 32 bits from fd
  fdInt <- liftIO $ ptrToBv32 bak ?ptrWidth fd

  -- Use llvm override for close
  resBv <- LCLS.callCloseFile bak memVar fs fdInt

  -- Pad result out to 64 bit pointer
  liftIO $ bvToPtr sym resBv ?ptrWidth

buildCloseOverride :: ( LCLM.HasLLVMAnn sym
                      , LCLM.HasPtrWidth w
                      )
                   => LCLS.LLVMFileSystem w
                   -> LCS.GlobalVar LCLM.Mem
                   -> Syscall p
                             sym
                             (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                             ext
                             (LCLM.LLVMPointerType w)
buildCloseOverride fs memVar =
  WI.withKnownNat ?ptrWidth $
  mkSyscall "close" $ \bak args ->
    Ctx.uncurryAssignment (callClose fs memVar bak) args

-- | This is identical to @crucible-llvm@'s @loadFileIdent@ function,
-- except that it uses the verifier's 'AExt.loadString' function instead of
-- @crucible-llvm@'s own 'LCLM.loadString' function.
loadFileIdent ::
  ( LCB.IsSymBackend sym bak
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , p ~ AExt.AmbientSimulatorState sym arch
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  Map.Map (DMC.MemWord w) String ->
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  LCS.OverrideSim p sym ext r args ret (LCSym.FileIdent sym)
loadFileIdent bak initialMem unsupportedRelocs filename_ptr =
  do let mvar = AM.imMemVar initialMem
     mem <- LCS.readGlobal mvar
     filename_bytes <- AExt.loadConcreteString bak mem initialMem unsupportedRelocs filename_ptr Nothing
     liftIO $ WI.stringLit (LCB.backendGetSym bak) (WI.Char8Literal (BS.pack filename_bytes))

-- | This is taken directly from @crucible-llvm@ with no changes. (We could
-- reexport it from "Lang.Crucible.LLVM.SymIO", but its implementation is so
-- small that it's probably not worth the bother.)
returnIOError32 ::
  LCB.IsSymInterface sym =>
  LCS.OverrideSim p sym ext r args ret (WI.SymBV sym 32)
returnIOError32 = do
  sym <- LCS.getSymInterface
  liftIO $ WI.bvLit sym (WI.knownNat @32) (BVS.mkBV (WI.knownNat @32) (-1))
