{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.FunctionOverride.X86_64.Linux (
    x86_64LinuxIntegerArguments
  , x86_64LinuxIntegerReturnRegisters
  , x86_64LinuxFunctionABI
  , x86_64LinuxTypes
  ) where

import           Control.Monad.IO.Class ( liftIO )
import           Data.Foldable ( foldl' )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Macaw.Memory as DMM
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           GHC.TypeNats ( type (<=), KnownNat )
import qualified Prettyprinter as PP

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Data.Macaw.X86 as DMX
import qualified Data.Macaw.X86.X86Reg as DMXR
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LCLMP
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.BaseTypes as WT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Extensions as AE
import qualified Stubs.Override as AO
import qualified Stubs.Panic as AP
import qualified Stubs.FunctionOverride as AF
import qualified Stubs.FunctionOverride.Common as AFC
import qualified Stubs.FunctionOverride.Extension as AFE
import qualified Stubs.FunctionOverride.StackArguments as AFS
import qualified Stubs.FunctionOverride.X86_64.Linux.Specialized as AFXLS
import qualified Stubs.Verifier.Concretize as AVC

-- | Extract integer arguments from the corresponding six x86_64 registers.
-- Any additional arguments are read from the stack at @8(%rsp)@, @16(%rsp)@,
-- etc.
x86_64LinuxIntegerArguments
  :: forall atps sym bak mem
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     )
  => bak
  -> DMS.GenArchVals mem DMX.X86_64
  -- ^ x86_64-specific architecture information
  -> LCT.CtxRepr atps
  -- ^ Types of argument registers
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes DMX.X86_64)
  -- ^ Argument register values
  -> LCLM.MemImpl sym
  -- ^ The memory state at the time of the function call
  -> IO (Ctx.Assignment (LCS.RegEntry sym) atps, AF.GetVarArg sym)
x86_64LinuxIntegerArguments bak archVals argTypes regs mem = do
  let ?ptrWidth = ptrWidth
  let stackArgList =
        map (AFS.loadIntegerStackArgument bak archVals regs mem)
             -- Note that we are starting the indices for stack arguments at 1,
             -- not 0, as the first stack argument is located at @8(%rsp)@
             -- instead of @0(%rsp)@ (which is where the return address
             -- resides).
             [1..]
  let argList = regArgList ++ stackArgList
  AO.buildArgumentAssignment bak argTypes argList
  where
    ptrWidth = WI.knownNat @64
    regArgList = map (pure . DMS.lookupReg archVals (LCS.RegEntry LCT.knownRepr regs)) DMX.x86ArgumentRegs

-- | Assemble x86_64 integer return register state from override return value.
x86_64LinuxIntegerReturnRegisters
  :: forall p sym bak ext r args rtp t mem
   . ( LCB.IsSymBackend sym bak )
  => bak
  -> DMS.GenArchVals mem DMX.X86_64
  -- ^ x86_64-specific architecture information
  -> LCT.TypeRepr t
  -- ^ Override return type
  -> AF.OverrideResult sym DMX.X86_64 t
  -- ^ Override's return value
  -> LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64)
  -- ^ Argument register values from before override execution
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64))
x86_64LinuxIntegerReturnRegisters bak archVals ovTyp result initRegs = do
  case ovTyp of
    LCT.UnitRepr -> do
      pure $ updateRegs initRegs (AF.regUpdates result)
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @64) -> do
      pure $ updateRegs initRegs ((DMXR.RAX, AF.result result) : AF.regUpdates result)
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @8) -> do
      regs <- bvZextResult result
      pure $ updateRegs regs (AF.regUpdates result)
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @16) -> do
      regs <- bvZextResult result
      pure $ updateRegs regs (AF.regUpdates result)
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @32) -> do
      regs <- bvZextResult result
      pure $ updateRegs regs (AF.regUpdates result)
    _ -> AP.panic AP.FunctionOverride
                  "x86_64LinuxIntegerReturnRegisters"
                  ["Unsupported override return type: " ++ show ovTyp]
    -- NOTE: If we encounter an override that returns a 128 bit int we'll
    -- need to add support for that here
  where
    sym = LCB.backendGetSym bak

    -- | Zero extend result LLMVPointer in region 0 (a bitvector) to fit in an
    -- integer register
    bvZextResult
      :: (1 <= srcW, KnownNat srcW)
      => AF.OverrideResult sym DMX.X86_64 (LCLM.LLVMPointerType srcW)
      -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64))
    bvZextResult ovRes = do
      asBv <- liftIO $ LCLM.projectLLVM_bv bak (AF.result ovRes)
      asPtr <- liftIO $ AO.bvToPtr sym asBv (WI.knownNat @64)
      return $ updateRegs initRegs [(DMXR.RAX, asPtr)]

    updateRegs :: LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64)
               -> [( DMC.ArchReg DMX.X86_64 (DMT.BVType 64)
                   , LCLM.LLVMPtr sym 64)]
               -> LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64)
    updateRegs regs regUpdates =
      foldl' (\r (reg, val) ->
               LCS.regValue $ DMS.updateReg archVals
                                            (LCS.RegEntry LCT.knownRepr r)
                                            reg
                                            val)
             regs
             regUpdates

-- | Retrieve the return address for the function being called by looking up
-- the first argument on the stack.
x86_64LinuxReturnAddr ::
  forall bak mem sym solver scope st fs.
     ( bak ~ LCBO.OnlineBackend solver scope st fs
     , sym ~ WE.ExprBuilder scope st fs
     , LCB.IsSymBackend sym bak
     , WPO.OnlineSolver solver
     , ?memOpts :: LCLM.MemOptions
     , LCLM.HasLLVMAnn sym
     )
  => bak
  -> DMS.GenArchVals mem DMX.X86_64
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes DMX.X86_64)
  -- ^ Registers to extract LR from
  -> LCLM.MemImpl sym
  -- ^ The memory state at the time of the function call
  -> IO (Maybe (DMM.MemWord 64))
x86_64LinuxReturnAddr bak archVals regs mem = do
  let ?ptrWidth = WI.knownNat @64
  addrPtr <- LCLM.doLoad bak mem
               (LCS.regValue stackPointer)
               (LCLM.bitvectorType 8)
               (LCLM.LLVMPointerRepr ?ptrWidth)
               LCLD.noAlignment
  res <- AVC.resolveSymBVAs bak WT.knownNat $ LCLMP.llvmPointerOffset addrPtr
  case res of
    Left AVC.UnsatInitialAssumptions -> do
      loc <- WI.getCurrentProgramLoc sym
      AP.panic AP.FunctionOverride "x86_64LinuxReturnAddr"
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

    stackPointer :: LCS.RegEntry sym (LCLM.LLVMPointerType 64)
    stackPointer = DMS.lookupReg archVals regsEntry DMXR.RSP

    regsEntry :: LCS.RegEntry sym (LCT.StructType (DMS.MacawCrucibleRegTypes DMX.X86_64))
    regsEntry = LCS.RegEntry (LCT.StructRepr (DMS.crucArchRegTypes (DMS.archFunctions archVals))) regs

x86_64LinuxFunctionABI :: ( LCLM.HasLLVMAnn sym
                          , ?memOpts :: LCLM.MemOptions )
                       => AF.BuildFunctionABI DMX.X86_64 sym (AE.AmbientSimulatorState sym DMX.X86_64)
x86_64LinuxFunctionABI = AF.BuildFunctionABI $ \fovCtx fs initialMem archVals unsupportedRelocs addrOvs namedOvs otherGlobs ->
  let ?ptrWidth = PN.knownNat @64 in
  let (nameMap, globMap) = AFC.mkFunctionNameGlobMaps
                             fovCtx fs initialMem unsupportedRelocs namedOvs
                             otherGlobs AFXLS.x86_64LinuxSpecializedOverrides
  in AF.FunctionABI { AF.functionIntegerArguments = \bak ->
                        x86_64LinuxIntegerArguments bak archVals
                    , AF.functionIntegerArgumentRegisters = DMX.x86ArgumentRegs
                    , AF.functionIntegerReturnRegisters = x86_64LinuxIntegerReturnRegisters
                    , AF.functionReturnAddr = x86_64LinuxReturnAddr
                    , AF.functionNameMapping = nameMap
                    , AF.functionGlobalMapping = globMap
                    , AF.functionAddrMapping = addrOvs
                    }

-- | A lookup function from 'AFE.TypeAlias' to types with the appropriate width
-- on X86_64 Linux.
x86_64LinuxTypes :: AFE.TypeLookup
x86_64LinuxTypes = AFE.TypeLookup $ \tp ->
  case tp of
    AFE.Byte -> Some (LCT.BVRepr (PN.knownNat @8))
    AFE.Int -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Long -> Some (LCT.BVRepr (PN.knownNat @64))
    AFE.PidT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Pointer -> Some (LCLM.LLVMPointerRepr (PN.knownNat @64))
    AFE.Short -> Some (LCT.BVRepr (PN.knownNat @16))
    AFE.SizeT -> Some (LCT.BVRepr (PN.knownNat @64))
    AFE.UidT -> Some (LCT.BVRepr (PN.knownNat @32))
