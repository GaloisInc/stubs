{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Stubs.Loader (
    withBinary,
    FunABIExt(..)
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe )
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Vector.NonEmpty as NEV
import           GHC.TypeLits ( type (<=) )
import qualified System.FilePath as SF

import qualified Data.ElfEdit as DE
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import           Data.Macaw.BinaryLoader.X86 ()
import           Data.Macaw.BinaryLoader.AArch32 ()
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.ElfLoader.PLTStubs as DMMEP
import qualified Data.Macaw.Memory.LoadCommon as MML
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.PPC as DMP
import           Data.Macaw.PPC.Symbolic ()
import qualified Data.Macaw.X86 as DMX
import           Data.Macaw.X86.Symbolic ()
import qualified Data.Macaw.ARM as Macaw.AArch32
import           Data.Macaw.AArch32.Symbolic ()
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified PE.Parser as PE

import qualified Stubs.ABI as AA
import qualified Stubs.Exception as AE
import qualified Stubs.Extensions as AExt
import qualified Stubs.FunctionOverride.Extension as AFE
import qualified Stubs.FunctionOverride.X86_64.Linux as AFXL
import qualified Stubs.FunctionOverride.AArch32.Linux as AFAL
import qualified Stubs.FunctionOverride.PPC.Linux as AFPL
import qualified Stubs.Loader.BinaryConfig as ALB
import qualified Stubs.Loader.ELF.DynamicLoader as ALED
import qualified Stubs.Loader.ELF.Symbols as ALES
import qualified Stubs.Loader.ELF.Symbols.AArch32 as ALESA
import qualified Stubs.Loader.Relocations as ALR
import qualified Stubs.Loader.Versioning as ALV
import qualified Stubs.Memory.AArch32.Linux as AMAL
import qualified Stubs.Memory.X86_64.Linux as AMXL
import qualified Stubs.Memory.PPC.Linux as AMPL
import qualified Stubs.Syscall.AArch32.Linux as ASAL
import qualified Stubs.Syscall.PPC.Linux as ASPL
import qualified Stubs.Syscall.X86_64.Linux as ASXL
import Data.Macaw.CFG (ArchReg, ArchAddrWidth)
import Data.Macaw.Types (BVType)
import Data.Macaw.X86.X86Reg as DMX
import qualified Stubs.Preamble as SPR
import Stubs.Arch.X86 ()
import Stubs.Arch.AArch32 ()
import Stubs.Arch.PPC32 ()
import Stubs.Arch.PPC64 ()
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import qualified Dismantle.PPC as DP
import qualified Language.ASL.Globals as ASL
import qualified Stubs.Translate.Core as STC
import qualified Stubs.Memory as SM
import qualified Stubs.Translate.Intrinsic as STI
import qualified Stubs.Extensions as SE
import qualified Stubs.Common as SC
import qualified What4.Interface as WI

data FunABIExt arch = FunABIExt {
  abiExtArchReg :: ArchReg arch (BVType (ArchAddrWidth arch))
}
-- | Load a bytestring as a binary image and associate it with a macaw
-- 'DMA.ArchitectureInfo' suitable for analyzing it
--
-- This currently supports ELF files and has some ability to recognize (but not
-- load) PE files.
--
-- In the continuation argument, one would invoke code discovery via macaw.
--
-- Note that the @sym@ parameter is only required to avoid a proxy.
--
-- NOTE: The memory model here is fixed to LLVMMemory. In future, this should be configurable in some way.
withBinary
  :: forall m sym a
   . ( CMC.MonadThrow m
     , MonadIO m
     , LCLM.HasLLVMAnn sym
     , WI.IsExprBuilder sym
     )
  => FilePath
  -- ^ Path to binary
  -> BS.ByteString
  -- ^ Binary contents
  -> Maybe FilePath
  -- ^ Path to directory containing @.so@ files
  -> LCF.HandleAllocator
  -> SC.Sym sym
  -> ( forall arch binFmt mem p w
      . ( DMB.BinaryLoader arch binFmt
        , 16 <= DMC.ArchAddrWidth arch
        , DMS.SymArchConstraints arch
        , SPR.Preamble arch
        , STC.StubsArch arch
        , STI.OverrideArch arch
        , mem ~ DMS.LLVMMemory
        , p ~ AExt.AmbientSimulatorState sym arch
        , w ~ DMC.RegAddrWidth (DMC.ArchReg arch)
        , 1 <= w
        , SM.IsStubsMemoryModel mem arch
        , SM.PtrType DMS.LLVMMemory arch ~ LCLM.LLVMPointerType (DMC.ArchAddrWidth arch)
        , SM.MemType DMS.LLVMMemory arch ~ LCLM.Mem
        , SM.VerifierState sym DMS.LLVMMemory arch ~ SE.AmbientSimulatorState sym arch
        )
     => DMA.ArchitectureInfo arch
     -> AA.ABI
     -> DMS.GenArchVals mem arch
     -> SM.BuildSyscallABI arch sym p mem
     -> SM.BuildFunctionABI arch sym p mem
     -> LCSC.ParserHooks (DMS.MacawExt arch)
     -> Int
     -- ^ Total number of bytes loaded (includes shared libraries).
     -> ALB.BinaryConfig arch binFmt
     -> Maybe (FunABIExt arch)
     -> [STI.OverrideModule arch]
     -- ^ Information about the loaded binaries
     -> m a)
  -> m a
withBinary name bytes mbSharedObjectDir hdlAlloc _sym k = do
  let ?memOpts = LCLM.laxPointerMemOptions
  case DE.decodeElfHeaderInfo bytes of
    Right (DE.SomeElf ehi) -> do
      -- See Note [ELF Load Options]
      let hdr = DE.header ehi
      let hdrMachine = DE.headerMachine hdr
      let hdrClass = DE.headerClass hdr
      let options = MML.defaultLoadOptions
      case (hdrMachine, hdrClass) of
        (DE.EM_X86_64, DE.ELFCLASS64) -> do
          fsbaseGlob <- liftIO $ AMXL.freshFSBaseGlobalVar hdlAlloc
          gsbaseGlob <- liftIO $ AMXL.freshGSBaseGlobalVar hdlAlloc
          let extOverride = AMXL.x86_64LinuxStmtExtensionOverride fsbaseGlob
                                                                  gsbaseGlob
          let mArchVals = DMS.archVals (Proxy @DMX.X86_64) (Just extOverride)
          case mArchVals of
            Just archVals -> do
              binsAndPaths <- loadElfBinaries options ehi hdrMachine hdrClass
              let bins = NEV.map fst binsAndPaths
              binConf <- mkElfBinConf DMX.x86_64PLTStubInfo
                                      options
                                      ehi
                                      binsAndPaths
                                      -- NOTE: We do not currently support
                                      -- relocations on X86 so we pass in empty
                                      -- maps for the relocation structures
                                      -- (see ticket #98).
                                      Map.empty
                                      Map.empty
                                      Map.empty
              -- Here we capture all of the necessary constraints required by the
              -- callback and pass them down along with the architecture info
              ovs <- STI.buildOverrides
              k DMX.x86_64_linux_info
                AA.X86_64Linux
                archVals
                ASXL.x86_64LinuxSyscallABI
                AFXL.x86_64LinuxFunctionABI
                (AFE.machineCodeParserHooks (Proxy @DMX.X86_64)
                                            AFXL.x86_64LinuxTypes)
                (elfBinarySizeTotal bins)
                binConf
                (Just (FunABIExt DMX.RAX))
                ovs
            Nothing -> CMC.throwM (AE.UnsupportedELFArchitecture name DE.EM_X86_64 DE.ELFCLASS64)
        (DE.EM_ARM, DE.ELFCLASS32) -> do
          tlsGlob <- liftIO $ AMAL.freshTLSGlobalVar hdlAlloc
          let extOverride = AMAL.aarch32LinuxStmtExtensionOverride
          case DMS.archVals (Proxy @Macaw.AArch32.ARM) (Just extOverride) of
            Just archVals -> do
              binsAndPaths <- loadElfBinaries options ehi hdrMachine hdrClass
              let bins = NEV.map fst binsAndPaths
              (unsupportedRels, supportedRels) <- liftIO $ ALESA.elfAarch32Rels bins
              let dynGlobSymMap = ALES.elfDynamicGlobalSymbolMap supportedRels bins
              binConf <- mkElfBinConf Macaw.AArch32.armPLTStubInfo
                                      options
                                      ehi
                                      binsAndPaths
                                      dynGlobSymMap
                                      unsupportedRels
                                      supportedRels
              ovs <- STI.buildOverrides
              k Macaw.AArch32.arm_linux_info
                AA.AArch32Linux
                archVals
                ASAL.aarch32LinuxSyscallABI
                (AFAL.aarch32LinuxFunctionABI tlsGlob)
                (AFE.machineCodeParserHooks (Proxy @Macaw.AArch32.ARM)
                                            AFAL.aarch32LinuxTypes)
                (elfBinarySizeTotal bins)
                binConf
                (Just (FunABIExt (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0"))))
                ovs
            Nothing -> CMC.throwM (AE.UnsupportedELFArchitecture name DE.EM_ARM DE.ELFCLASS32)
        (DE.EM_PPC, DE.ELFCLASS32) -> do
          let extOverride = AMPL.ppcLinuxStmtExtensionOverride
          case DMS.archVals (Proxy @DMP.PPC32) (Just extOverride) of
            Just archVals -> do
              binsAndPaths <- loadElfBinaries options ehi hdrMachine hdrClass
              let bins = NEV.map fst binsAndPaths
              binConf <- mkElfBinConf (DMMEP.noPLTStubInfo "PPC32")
                                      options
                                      ehi
                                      binsAndPaths
                                      -- NOTE: We do not currently support
                                      -- relocations on PowerPC
                                      -- (see https://github.com/GaloisInc/macaw/issues/386)
                                      -- so we pass in empty maps for the
                                      -- relocation structures.
                                      Map.empty
                                      Map.empty
                                      Map.empty
              -- Here we capture all of the necessary constraints required by the
              -- callback and pass them down along with the architecture info
              ovs <- STI.buildOverrides
              k DMP.ppc32_linux_info
                AA.PPC32Linux
                archVals
                ASPL.ppcLinuxSyscallABI
                AFPL.ppcLinuxFunctionABI
                (AFE.machineCodeParserHooks (Proxy @DMP.PPC32)
                                            AFPL.ppc32LinuxTypes)
                (elfBinarySizeTotal bins)
                binConf
                (Just (FunABIExt (DMP.PPC_GP (DP.GPR 3))))
                ovs
            Nothing -> CMC.throwM (AE.UnsupportedELFArchitecture name DE.EM_PPC DE.ELFCLASS32)
        (DE.EM_PPC64, DE.ELFCLASS64) -> do
          let extOverride = AMPL.ppcLinuxStmtExtensionOverride
          case DMS.archVals (Proxy @DMP.PPC64) (Just extOverride) of
            Just archVals -> do
              binsAndPaths <- loadElfBinaries options ehi hdrMachine hdrClass
              let bins = NEV.map fst binsAndPaths
              binConf <- mkElfBinConf (DMMEP.noPLTStubInfo "PPC64")
                                      options
                                      ehi
                                      binsAndPaths
                                      -- NOTE: We do not currently support
                                      -- relocations on PowerPC
                                      -- (see https://github.com/GaloisInc/macaw/issues/386)
                                      -- so we pass in empty maps for the
                                      -- relocation structures.
                                      Map.empty
                                      Map.empty
                                      Map.empty
              -- Here we capture all of the necessary constraints required by the
              -- callback and pass them down along with the architecture info
              ovs <- STI.buildOverrides
              k (DMP.ppc64_linux_info (ALB.lbpBinary (ALB.mainLoadedBinaryPath binConf)))
                AA.PPC64Linux
                archVals
                ASPL.ppcLinuxSyscallABI
                AFPL.ppcLinuxFunctionABI
                (AFE.machineCodeParserHooks (Proxy @DMP.PPC64)
                                            AFPL.ppc64LinuxTypes)
                (elfBinarySizeTotal bins)
                binConf
                (Just (FunABIExt (DMP.PPC_GP (DP.GPR 3))))
                ovs
            Nothing -> CMC.throwM (AE.UnsupportedELFArchitecture name DE.EM_PPC64 DE.ELFCLASS64)
        (machine, klass) -> CMC.throwM (AE.UnsupportedELFArchitecture name machine klass)
    Left _ -> throwDecodeFailure name bytes
  where
    -- Load the main binary and any shared objects
    loadElfBinaries
      :: (DMB.BinaryLoader arch (DE.ElfHeaderInfo w))
      => MML.LoadOptions
      -> DE.ElfHeaderInfo w
      -> DE.ElfMachine
      -> DE.ElfClass w
      -> m (NEV.NonEmptyVector (DMB.LoadedBinary arch (DE.ElfHeaderInfo w), FilePath))
    loadElfBinaries options ehi hdrMachine hdrClass = do
      lb <- DMB.loadBinary options ehi
      let sharedObjectDir = fromMaybe (SF.takeDirectory name) mbSharedObjectDir
      sos <- ALED.loadDynamicDependencies hdrMachine hdrClass sharedObjectDir lb name
      pure $ NEV.fromNonEmpty $ (lb, name) NEL.:| sos

    -- Construct a BinaryConfig for an ELF file.
    mkElfBinConf ::
      forall arch binFmt w reloc.
      ( binFmt ~ DE.ElfHeaderInfo (DMC.ArchAddrWidth arch)
      , w ~ DMC.ArchAddrWidth arch
      , w ~ DE.RelocationWidth reloc
      , Integral (DE.ElfWordType w)
      , DE.IsRelocationType reloc
      , DMM.MemWidth w
      ) =>
      DMMEP.PLTStubInfo reloc ->
      MML.LoadOptions ->
      DE.ElfHeaderInfo w ->
      -- ^ The relocation type to use when detecting PLT stubs
      NEV.NonEmptyVector (DMB.LoadedBinary arch binFmt, FilePath) ->
      -- ^ All loaded binaries (including shared libraries) and their file paths
      Map.Map ALV.VersionedGlobalVarName (DMM.MemWord (DMC.ArchAddrWidth arch)) ->
      -- ^ Mapping from exported, dynamic, global variable names to addresses
      Map.Map (DMM.MemWord (DMC.ArchAddrWidth arch)) String ->
      -- ^ Unsupported relocations.  Mapping from addresses to names of
      -- unsupported relocation types.
      Map.Map (DMM.MemWord (DMC.ArchAddrWidth arch)) ALR.RelocType ->
      -- ^ Supported relocation types
      m (ALB.BinaryConfig arch binFmt)
    mkElfBinConf pltStubInfo options ehi binsAndPaths dynGlobals
                 unsupportedRels supportedRels = do
      let pltStubs =
            fmap
              (\(symtabEntry, versionedVal) ->
                ALV.VerSym
                  { ALV.versymSymbol =
                      ALES.symtabEntryFunctionName symtabEntry
                  , ALV.versymVersion =
                      ALES.versionTableValueToSymbolVersion versionedVal
                  })
              (DMMEP.pltStubSymbols pltStubInfo options ehi)
      let loadedBinaryPaths =
            NEV.map
              (\(bin, path) ->
                ALB.LoadedBinaryPath
                  { ALB.lbpBinary = bin
                  , ALB.lbpPath = path
                  , ALB.lbpEntryPoints = ALES.elfEntryPointAddrMap bin
                  , ALB.lbpGlobalVars = ALES.elfGlobalSymbolMap supportedRels bin
                  , ALB.lbpPltStubs = pltStubs
                  })
              binsAndPaths
      let bins = NEV.map fst binsAndPaths
      let dynFuncSymMap = ALES.elfDynamicFuncSymbolMap supportedRels bins
      return ALB.BinaryConfig
        { ALB.bcBinaries = loadedBinaryPaths
        , ALB.bcMainBinarySymbolMap = ALES.elfEntryPointSymbolMap supportedRels $ NEV.head bins
        , ALB.bcDynamicFuncSymbolMap = dynFuncSymMap
        , ALB.bcDynamicGlobalVarAddrs = dynGlobals
        , ALB.bcPltStubs = Map.unions $ fmap ALB.lbpPltStubs loadedBinaryPaths
        , ALB.bcUnsuportedRelocations = unsupportedRels
        , ALB.bcSupportedRelocations = supportedRels
        }

    -- The total size (in bytes) of a collection of ELF binaries.
    elfBinarySizeTotal ::
      (Foldable f, Functor f) =>
      f (DMB.LoadedBinary arch (DE.ElfHeaderInfo w)) ->
      Int
    elfBinarySizeTotal = sum . fmap (BS.length . DE.headerFileContents . DMB.originalBinary)

    throwDecodeFailure elfName elfBytes =
      case PE.decodePEHeaderInfo (BSL.fromStrict elfBytes) of
        Right (Some _) -> CMC.throwM (AE.UnsupportedPEArchitecture elfName)
        Left _ -> CMC.throwM (AE.UnsupportedBinaryFormat elfName)

{- Note [ELF Load Options]

We are using the default load options here. We may want to change the load
offset at some point, which would allow us to vary the address at which the
binary is loaded.  While we won't be able to make the load offset symbolic here,
it would allow us to test a few concrete cases.

-}
