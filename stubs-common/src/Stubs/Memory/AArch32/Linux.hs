{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Stubs.Memory.AArch32.Linux (
    aarch32LinuxInitGlobals
  , aarch32LinuxStmtExtensionOverride
    -- * TLS
  , freshTLSGlobalVar
  ) where

import qualified Data.BitVector.Sized as BVS
import qualified Data.Text as DT

import qualified Data.Macaw.ARM as DMA
 -- Sometimes, GHC is unable to find instances of RegAddrWidth that are
 -- available by way of transitive module imports. The only reliable way of
 -- preventing this issue that I've found is to import the defining module for
 -- the instances directly. This is most likely a GHC bug (perhaps
 -- https://gitlab.haskell.org/ghc/ghc/-/issues/16234), but oh well.
import           Data.Macaw.ARM.ARMReg ()
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Common as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified What4.Interface as WI
import qualified What4.Symbol as WSym

import qualified Stubs.Memory as AM
import qualified Stubs.Common as SC
import qualified Lang.Crucible.LLVM.MemModel.Partial as LCLMP
import qualified Lang.Crucible.LLVM.Errors as LCLE
import qualified Lang.Crucible.LLVM.MemModel.CallStack
import qualified Lang.Crucible.Types as LCT
import qualified Data.Macaw.Symbolic.Memory as DMSM
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Parameterized.NatRepr as PN
import qualified Stubs.Memory as SM
import qualified SemMC.Architecture.AArch32 as SAA
import Control.Monad.IO.Class (liftIO)
import Data.Macaw.AArch32.Symbolic ()
import qualified Stubs.Extensions as SE
import qualified Data.Macaw.Symbolic.MemOps as DMSMO
import qualified Stubs.Extensions.Memory as AEM
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Stubs.Loader.BinaryConfig as SLB
import qualified Stubs.Memory.Common as SMC

instance SM.IsStubsMemoryModel DMS.LLVMMemory SAA.AArch32 where 
  type instance PtrType DMS.LLVMMemory SAA.AArch32 =  LCLM.LLVMPointerType (DMC.ArchAddrWidth SAA.AArch32)
  type instance MemType DMS.LLVMMemory SAA.AArch32 = LCLM.Mem
  type instance BVToPtrTy w DMS.LLVMMemory SAA.AArch32 = LCLM.LLVMPointerType w
  type instance MemTable sym DMS.LLVMMemory SAA.AArch32 = AEM.MemPtrTable sym SAA.AArch32
  type instance MemMap sym SAA.AArch32 = DMSMO.GlobalMap sym LCLM.Mem (DMC.ArchAddrWidth SAA.AArch32)

  type instance VerifierState sym DMS.LLVMMemory SAA.AArch32 = (SE.AmbientSimulatorState sym SAA.AArch32) 

  bvToPtr :: LCT.TypeRepr tp-> LCT.TypeRepr (SM.ToPtrTy tp DMS.LLVMMemory SAA.AArch32)
  bvToPtr (LCT.BVRepr n) = LCLM.LLVMPointerRepr n
  bvToPtr ty = case ty of 
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

  memPtrSize :: PN.NatRepr (DMC.ArchAddrWidth SAA.AArch32)
  memPtrSize = WI.knownRepr

  genStackPtr baseptr offset (SC.Sym sym _) = liftIO $ LCLM.ptrAdd sym WI.knownRepr baseptr offset

  initMem (SC.Sym sym bak) archInfo stackSize binConf halloc = do 
    let endian = DMSM.toCrucibleEndian (DMA.archEndianness archInfo)
    mem <- liftIO $ LCLM.emptyMem endian
    stackSizeBV <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackSize)
    let ?ptrWidth = SM.memPtrSize @DMS.LLVMMemory @SAA.AArch32
    (recordFn, _) <- liftIO SM.buildRecordLLVMAnnotation
    let ?recordLLVMAnnotation = recordFn
    let ?memOpts = LCLM.defaultMemOptions
    (stackBasePtr, mem1) <- liftIO $ LCLM.doMalloc bak LCLM.StackAlloc LCLM.Mutable "stack_alloc" mem stackSizeBV LCLD.noAlignment
    tlsvar <- liftIO $ freshTLSGlobalVar halloc
    (_, globals0) <- liftIO $ aarch32LinuxInitGlobals tlsvar (SC.Sym sym bak) mem1
    memVar <- liftIO $ LCLM.mkMemVar (DT.pack "ambient-verifier::memory") halloc
    let globals1 = LCSG.insertGlobal memVar mem1 globals0
    let mems = fmap (DMB.memoryImage . SLB.lbpBinary) (SLB.bcBinaries binConf)
    (_, memPtrTbl) <- AEM.newMemPtrTable (SMC.globalMemoryHooks mems mempty mempty) bak endian mems
    let globalMap = AEM.mapRegionPointers memPtrTbl

    return SM.InitialMemory{
      SM.imMemVar=memVar,
      SM.imGlobals=globals1,
      SM.imStackBasePtr=stackBasePtr,
      SM.imMemTable=memPtrTbl,
      SM.imGlobalMap=globalMap
    }
-- | TLS pointer memory size in bytes
tlsMemorySize :: Integer
tlsMemorySize = 4 * 1024

-- | Create and initialize a pointer to store the TLS value.
-- See @Note [AArch32 and TLS]@ in "Ambient.FunctionOverride.AArch32.Linux".
initTLSMemory :: ( LCB.IsSymBackend sym bak
                 , LCLM.HasLLVMAnn sym
                 , ?memOpts :: LCLM.MemOptions
                 )
              => bak
              -> LCLM.MemImpl sym
                 -- ^ MemImpl to add the TLS pointer to
              -> IO ( LCLM.LLVMPtr sym (DMC.ArchAddrWidth DMA.ARM)
                      -- Base pointer for new TLS pointer
                    , LCLM.MemImpl sym
                      -- Updated MemImpl containing new TLS pointer
                    )
initTLSMemory bak mem0 = do
  let sym = LCB.backendGetSym bak
  let ?ptrWidth = WI.knownRepr
  arrayStorage <- WI.freshConstant sym (WSym.safeSymbol "tls") WI.knownRepr
  tlsMemorySizeBV <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr tlsMemorySize)
  oneByte <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr 1)
  (tlsPtr, mem1) <-
    LCLM.doCalloc bak mem0 tlsMemorySizeBV oneByte LCLD.noAlignment
  mem2 <- LCLM.doArrayStore bak
                            mem1
                            tlsPtr
                            LCLD.noAlignment
                            arrayStorage
                            tlsMemorySizeBV
  pure (tlsPtr, mem2)

-- | Allocate a fresh global variable representing TLS state.
freshTLSGlobalVar ::
  LCF.HandleAllocator ->
  IO (LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMA.ARM)))
freshTLSGlobalVar hdlAlloc =
  LCCC.freshGlobalVar hdlAlloc
                      (DT.pack "tls")
                      (LCLM.LLVMPointerRepr (WI.knownNat @32))

-- | This function takes a global variable for the TLS pointer
-- and returns an 'InitArchSpecificGlobals' that initializes the global
-- and inserts it into the global variable state.
aarch32LinuxInitGlobals ::
     ( ?memOpts :: LCLM.MemOptions,
     ?recordLLVMAnnotation::Lang.Crucible.LLVM.MemModel.CallStack.CallStack -> LCLMP.BoolAnn sym -> LCLE.BadBehavior sym -> IO ()
     )
  => LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMA.ARM))
     -- ^ Global variable for TLS
  -> (SC.Sym sym -> LCLM.MemImpl sym-> IO (LCLM.MemImpl sym,LCSG.SymGlobalState sym ))
aarch32LinuxInitGlobals tlsGlob = \(SC.Sym _ bak) mem0 -> do
    (tlsPtr, mem1) <- initTLSMemory bak mem0
    return (mem1, LCSG.insertGlobal tlsGlob tlsPtr LCSG.emptyGlobals)

-- | There are currently no overrides for macaw-aarch32-symbolic
aarch32LinuxStmtExtensionOverride :: DMS.MacawArchStmtExtensionOverride DMA.ARM
aarch32LinuxStmtExtensionOverride =
  DMS.MacawArchStmtExtensionOverride $ \_ _ -> return Nothing
