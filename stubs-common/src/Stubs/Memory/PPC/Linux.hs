{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-| Description: IsStubsMemoryModel instance for LLVMMemory with PPC

-}
module Stubs.Memory.PPC.Linux (ppcLinuxStmtExtensionOverride) where

import qualified Data.BitVector.Sized as BVS
import qualified Data.Text as DT

import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified What4.Interface as WI
import qualified What4.Symbol as WSym

import qualified Stubs.Memory as AM
import qualified Stubs.Common as SC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.Types as LCT
import qualified Data.Macaw.Symbolic.Memory as DMSM
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Parameterized.NatRepr as PN
import qualified Stubs.Memory as SM
import qualified SemMC.Architecture.PPC as SAP
import Control.Monad.IO.Class (MonadIO(..))
import qualified Data.Macaw.PPC as DMP
import Data.Macaw.PPC.Symbolic ()
import qualified Stubs.Extensions as SE
import qualified Data.Macaw.Symbolic.MemOps as DMSMO
import qualified Stubs.Extensions.Memory as AEM
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Stubs.Loader.BinaryConfig as SLB
import qualified Stubs.Memory.Common as SMC

instance (DMS.SymArchConstraints (DMP.AnyPPC v), 16 WI.<= SAP.AddrWidth v) =>
    SM.IsStubsMemoryModel DMS.LLVMMemory (DMP.AnyPPC v) where
  type instance PtrType DMS.LLVMMemory (DMP.AnyPPC v) = LCLM.LLVMPointerType (SAP.AddrWidth v)
  type instance MemType DMS.LLVMMemory (DMP.AnyPPC v) = LCLM.Mem
  type instance BVToPtrTy w DMS.LLVMMemory (DMP.AnyPPC v) = LCLM.LLVMPointerType w
  type instance MemTable sym DMS.LLVMMemory (DMP.AnyPPC v) = AEM.MemPtrTable sym (DMP.AnyPPC v)
  type instance MemMap sym (DMP.AnyPPC v) = DMSMO.GlobalMap sym LCLM.Mem (SAP.AddrWidth v)

  type instance VerifierState sym DMS.LLVMMemory (DMP.AnyPPC v) = SE.AmbientSimulatorState sym (DMP.AnyPPC v)

  bvToPtr :: LCT.TypeRepr tp -> LCT.TypeRepr (SM.ToPtrTy tp DMS.LLVMMemory (DMP.AnyPPC v))
  bvToPtr ty = case ty of
    -- Map BVRepr to LLVMPointerRepr...
    LCT.BVRepr n -> LCLM.LLVMPointerRepr n

    -- ...and map all other TypeReprs to themselves.
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

  memPtrSize :: PN.NatRepr (SAP.AddrWidth v)
  memPtrSize = WI.knownRepr

  genStackPtr :: (Monad m, MonadIO m) => LCLM.LLVMPtr sym (SAP.AddrWidth v) -> WI.SymBV sym (SAP.AddrWidth v) -> SC.Sym sym -> m (LCLM.LLVMPtr sym (SAP.AddrWidth v))
  genStackPtr baseptr offset (SC.Sym sym _) = liftIO $ LCLM.ptrAdd sym WI.knownRepr baseptr offset

  initMem :: SC.Sym sym -> DMA.ArchitectureInfo (DMP.AnyPPC v) -> Integer -> SLB.BinaryConfig (DMP.AnyPPC v) binfmt -> LCF.HandleAllocator -> (Monad m, MonadIO m) => m (SM.InitialMemory sym DMS.LLVMMemory (DMP.AnyPPC v))
  initMem (SC.Sym sym bak) archInfo stackSize binConf halloc = do
    let endian = DMSM.toCrucibleEndian (DMA.archEndianness archInfo)

    let mems = fmap (DMB.memoryImage . SLB.lbpBinary) (SLB.bcBinaries binConf)
    let ?ptrWidth = SM.memPtrSize @DMS.LLVMMemory @(DMP.AnyPPC v)
    (recordFn, _) <- liftIO SM.buildRecordLLVMAnnotation
    let ?recordLLVMAnnotation = recordFn
    let ?memOpts = LCLM.defaultMemOptions
    (mem, memPtrTbl) <- AEM.newMemPtrTable (SMC.globalMemoryHooks mems mempty mempty) bak endian mems
    stackSizeBV <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackSize)

    (stackBasePtr, mem1) <- liftIO $ LCLM.doMalloc bak LCLM.StackAlloc LCLM.Mutable "stack_alloc" mem stackSizeBV LCLD.noAlignment

    stackArrayStorage <- liftIO $ WI.freshConstant sym (WSym.safeSymbol "stack_array") WI.knownRepr
    mem2 <- liftIO $ LCLM.doArrayStore bak mem1 stackBasePtr LCLD.noAlignment stackArrayStorage stackSizeBV

    memVar <- liftIO $ LCLM.mkMemVar (DT.pack "stubs::memory") halloc
    let globals = LCSG.insertGlobal memVar mem2 LCSG.emptyGlobals
    let globalMap = AEM.mapRegionPointers memPtrTbl

    return SM.InitialMemory{
      SM.imMemVar=memVar,
      SM.imGlobals=globals,
      SM.imStackBasePtr=stackBasePtr,
      SM.imMemTable=memPtrTbl,
      SM.imGlobalMap=globalMap
    }

-- | There are currently no overrides for macaw-ppc-symbolic
ppcLinuxStmtExtensionOverride :: DMS.MacawArchStmtExtensionOverride (DMP.AnyPPC v)
ppcLinuxStmtExtensionOverride =
  DMS.MacawArchStmtExtensionOverride $ \_ _ -> return Nothing
