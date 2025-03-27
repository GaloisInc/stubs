{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module provides definitions to support the Linux ABIs for 32-bit and
-- 64-bit PowerPC.
module Stubs.FunctionOverride.PPC.Linux (
    ppcLinuxIntegerArguments
  , ppcLinuxIntegerReturnRegisters
  , ppcLinuxReturnAddr
  , ppcLinuxFunctionABI
  , ppc32LinuxTypes
  , ppc64LinuxTypes
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import           Data.Foldable ( foldl' )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Prettyprinter as PP

import qualified Data.Macaw.PPC as DMP
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Dismantle.PPC as DP
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LCLMP
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified SemMC.Architecture.PPC as SAP
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Extensions as AE
import qualified Stubs.FunctionOverride as AF
import qualified Stubs.FunctionOverride.Common as AFC
import qualified Stubs.FunctionOverride.Extension as AFE
import qualified Stubs.FunctionOverride.StackArguments as AFS
import qualified Stubs.Override as AO
import qualified Stubs.Panic as AP
import qualified Stubs.Verifier.Concretize as AVC
import qualified Stubs.Memory.PPC.Linux ()
import qualified Stubs.Memory as SM

-- | Extract integer arguments from the corresponding eight PowerPC registers.
-- Any additional arguments are read from the stack at @8(r1)@, @16(r1)@, etc.
ppcLinuxIntegerArguments
  :: forall v atps sym bak mem
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , DMP.KnownVariant v
     , DMS.SymArchConstraints (DMP.AnyPPC v)
     , 16 WI.<= SAP.AddrWidth v
     )
  => bak
  -> DMS.GenArchVals mem (DMP.AnyPPC v)
  -- ^ PPC-specific architecture information
  -> LCT.CtxRepr atps
  -- ^ The argument types
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes (DMP.AnyPPC v))
  -- ^ A register structure containing symbolic values
  -> LCLM.MemImpl sym
  -- ^ The memory state at the time of the function call
  -> IO (Ctx.Assignment (LCS.RegEntry sym) atps, AF.GetVarArg sym)
ppcLinuxIntegerArguments bak archVals argTypes regs mem = do
  let ?ptrWidth = SAP.addrWidth (DMP.knownVariant @v)
  let stackArgList =
        map (AFS.loadIntegerStackArgument bak archVals regs mem)
             -- Note that we are starting the indices for stack arguments at 1,
             -- not 0, as the first stack argument is located at @8(r1)@
             -- instead of @0(r1)@ (which is where the back chain resides).
             [1..]
  -- NB: `regArgList` below only has eight elements, so the cost of using (++)
  -- below (which is O(n) in the size of the first list n) is negligible.
  let argList = regArgList ++ stackArgList
  AO.buildArgumentAssignment (LCB.backendGetSym bak) argTypes argList
  where
    regArgList = map (pure . DMS.lookupReg archVals (LCS.RegEntry LCT.knownRepr regs))
                     ppcLinuxIntegerArgumentRegisters

ppcLinuxIntegerArgumentRegisters ::
  (1 WI.<= SAP.AddrWidth v) =>
  [DMP.PPCReg v (DMT.BVType (SAP.AddrWidth v))]
ppcLinuxIntegerArgumentRegisters =
  [DMP.PPC_GP (DP.GPR i) | i <- [3..10]]

-- | Inject override return values back into the register state.
--
-- Void returns ('LCT.UnitRepr') have no effect.
--
-- Otherwise, an integer return value is placed into r3.
ppcLinuxIntegerReturnRegisters
  :: forall v sym bak mem tp p ext r args rtp
   . ( LCB.IsSymBackend sym bak
     , DMP.KnownVariant v
     , DMS.SymArchConstraints (DMP.AnyPPC v)
     , 1 WI.<= SAP.AddrWidth v
     )
  => bak
  -> DMS.GenArchVals mem (DMP.AnyPPC v)
  -> LCT.TypeRepr tp
  -> AF.OverrideResult sym (DMP.AnyPPC v) tp
  -> LCS.RegValue sym (DMS.ArchRegStruct (DMP.AnyPPC v))
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct (DMP.AnyPPC v)))
ppcLinuxIntegerReturnRegisters bak archVals ovTy result initRegs =
  case ovTy of
    LCT.UnitRepr ->
      pure $ updateRegs initRegs (AF.regUpdates result)
    _ -> do
      regs' <- injectIntoReg ovTy (AF.result result) r3 initRegs
      pure $ updateRegs regs' (AF.regUpdates result)
  where
    sym = LCB.backendGetSym bak
    r3 = DMP.PPC_GP (DP.GPR 3)

    -- Inject a return value of the given TypeRepr into the supplied PPCReg.
    -- Depending on the type of the value, this may require zero extension.
    injectIntoReg ::
         forall tp
       . LCT.TypeRepr tp
      -> LCS.RegValue sym tp
      -> DMP.PPCReg v (DMT.BVType (SAP.AddrWidth v))
      -> LCS.RegValue sym (DMS.ArchRegStruct (DMP.AnyPPC v))
      -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct (DMP.AnyPPC v)))
    injectIntoReg tpr val reg allRegs =
      case tpr of
        LCLM.LLVMPointerRepr w
          | Just WI.Refl <- WI.testEquality w (WI.knownNat @64) -> do
              val' <- liftIO $ extendOrTruncResult val
              return $! updateRegs allRegs [(reg, val')]
        LCLM.LLVMPointerRepr w
          | Just PC.Refl <- PC.testEquality w (PN.knownNat @32) -> do
              val' <- liftIO $ extendOrTruncResult val
              return $! updateRegs allRegs [(reg, val')]
        LCLM.LLVMPointerRepr w
          | Just PC.Refl <- PC.testEquality w (PN.knownNat @16) -> do
              val' <- liftIO $ extendOrTruncResult val
              return $! updateRegs allRegs [(reg, val')]
        LCLM.LLVMPointerRepr w
          | Just PC.Refl <- PC.testEquality w (PN.knownNat @8) -> do
              val' <- liftIO $ extendOrTruncResult val
              return $! updateRegs allRegs [(reg, val')]
        _ -> AP.panic AP.FunctionOverride "ppcLinuxIntegerReturnRegisters" [ "Unsupported return type: " ++ show tpr ]

    -- Zero-extend or truncate the return value to fit in a register and update
    -- the register state.
    extendOrTruncResult
      :: (1 WI.<= srcW, DMT.KnownNat srcW)
      => LCLM.LLVMPtr sym srcW
      -> IO (LCLM.LLVMPtr sym (SAP.AddrWidth v))
    extendOrTruncResult res =
      AO.adjustPointerSize sym res (SAP.addrWidth (DMP.knownVariant @v))

    updateRegs ::
         LCS.RegValue sym (DMS.ArchRegStruct (DMP.AnyPPC v))
      -> [( DMP.PPCReg v (DMT.BVType (SAP.AddrWidth v))
          , LCLM.LLVMPtr sym (SAP.AddrWidth v))]
      -> LCS.RegValue sym (DMS.ArchRegStruct (DMP.AnyPPC v))
    updateRegs regs regUpdates =
      foldl' (\r (reg, val) ->
               LCS.regValue $ DMS.updateReg archVals
                                            (LCS.RegEntry LCT.knownRepr r)
                                            reg
                                            val)
             regs
             regUpdates

-- | Retrieve the return address for the function being called by looking up
-- the current value of the link register.
ppcLinuxReturnAddr ::
  forall bak mem sym v solver scope st fs.
     ( bak ~ LCBO.OnlineBackend solver scope st fs
     , sym ~ WE.ExprBuilder scope st fs
     , LCB.IsSymBackend sym bak
     , WPO.OnlineSolver solver
     , DMP.KnownVariant v
     , DMM.MemWidth (SAP.AddrWidth v)
     , DMS.SymArchConstraints (DMP.AnyPPC v)
     )
  => bak
  -> DMS.GenArchVals mem (DMP.AnyPPC v)
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes (DMP.AnyPPC v))
  -- ^ Registers to extract link register from
  -> LCLM.MemImpl sym
  -- ^ The memory state at the time of the function call
  -> IO (Maybe (DMM.MemWord (SAP.AddrWidth v)))
ppcLinuxReturnAddr bak archVals regs _mem = do
  let addrSymBV = LCLMP.llvmPointerOffset $ LCS.regValue
                                          $ DMS.lookupReg archVals regsEntry DMP.PPC_LNK
  res <- AVC.resolveSymBVAs bak (SAP.addrWidth (DMP.knownVariant @v)) addrSymBV
  case res of
    Left AVC.UnsatInitialAssumptions -> do
      loc <- WI.getCurrentProgramLoc sym
      AP.panic AP.FunctionOverride "ppcLinuxReturnAddr"
        ["Initial assumptions are unsatisfiable at " ++ show (PP.pretty (WP.plSourceLoc loc))]

    -- This can genuinely happen if a function is invoked as a tail call, so
    -- which the main reason why this returns a Maybe instead of panicking.
    Left AVC.MultipleModels ->
      pure Nothing

    -- I'm unclear if this case can ever happen under normal circumstances, but
    -- we'll return Nothing here just to be on the safe side.
    Left AVC.SolverUnknown ->
      pure Nothing

    Right addrBV ->
      pure $ Just $ fromIntegral $ BVS.asUnsigned addrBV
  where
    sym = LCB.backendGetSym bak

    regsEntry :: LCS.RegEntry sym (LCT.StructType (DMS.MacawCrucibleRegTypes (DMP.AnyPPC v)))
    regsEntry = LCS.RegEntry (LCT.StructRepr (DMS.crucArchRegTypes (DMS.archFunctions archVals))) regs

ppcLinuxFunctionABI ::
     forall v sym
   . ( ?memOpts :: LCLM.MemOptions
     , LCLM.HasLLVMAnn sym
     , DMP.KnownVariant v
     , DMM.MemWidth (SAP.AddrWidth v)
     , DMS.SymArchConstraints (DMP.AnyPPC v)
     , 16 WI.<= SAP.AddrWidth v
     )
  => SM.BuildFunctionABI (DMP.AnyPPC v) sym (AE.AmbientSimulatorState sym (DMP.AnyPPC v)) DMS.LLVMMemory
ppcLinuxFunctionABI = SM.BuildFunctionABI $ \_fovCtx _initialMem archVals _unsupportedRelocs addrOvs namedOvs otherGlobs ->
  let ?ptrWidth = SAP.addrWidth (DMP.knownVariant @v) in
  let (nameMap, globMap) = AFC.mkFunctionNameGlobMaps @(DMP.AnyPPC v) namedOvs
                             otherGlobs [] in
  SM.FunctionABI {
                   SM.functionIntegerArguments = \bak ->
                     ppcLinuxIntegerArguments bak archVals
                 , SM.functionIntegerArgumentRegisters = ppcLinuxIntegerArgumentRegisters
                 , SM.functionIntegerReturnRegisters = ppcLinuxIntegerReturnRegisters
                 , SM.functionReturnAddr = ppcLinuxReturnAddr
                 , SM.functionNameMapping = nameMap
                 , SM.functionGlobalMapping = globMap
                 , SM.functionAddrMapping = addrOvs
                 }

-- | A lookup function from 'AFE.TypeAlias' to types with the appropriate width
-- on PPC32 Linux.
ppc32LinuxTypes :: AFE.TypeLookup
ppc32LinuxTypes = AFE.TypeLookup $ \tp ->
  case tp of
    AFE.Byte -> Some (LCT.BVRepr (PN.knownNat @8))
    AFE.Int -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Long -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.PidT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Pointer -> Some (LCLM.LLVMPointerRepr (PN.knownNat @32))
    AFE.Short -> Some (LCT.BVRepr (PN.knownNat @16))
    AFE.SizeT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.UidT -> Some (LCT.BVRepr (PN.knownNat @32))

-- | A lookup function from 'AFE.TypeAlias' to types with the appropriate width
-- on PPC64 Linux.
ppc64LinuxTypes :: AFE.TypeLookup
ppc64LinuxTypes = AFE.TypeLookup $ \tp ->
  case tp of
    AFE.Byte -> Some (LCT.BVRepr (PN.knownNat @8))
    AFE.Int -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Long -> Some (LCT.BVRepr (PN.knownNat @64))
    AFE.PidT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Pointer -> Some (LCLM.LLVMPointerRepr (PN.knownNat @64))
    AFE.Short -> Some (LCT.BVRepr (PN.knownNat @16))
    AFE.SizeT -> Some (LCT.BVRepr (PN.knownNat @64))
    AFE.UidT -> Some (LCT.BVRepr (PN.knownNat @32))
