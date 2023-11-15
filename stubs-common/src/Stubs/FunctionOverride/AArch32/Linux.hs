{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module provides definitions to support the 32 bit Linux ABI for AArch32
--
-- See <https://github.com/ARM-software/abi-aa/releases> for details
module Stubs.FunctionOverride.AArch32.Linux (
    aarch32LinuxIntegerArguments
  , aarch32LinuxIntegerReturnRegisters
  , aarch32LinuxFunctionABI
  , aarch32LinuxTypes
  ) where

import           Control.Lens ( use )
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import           Data.Foldable ( foldl' )
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Prettyprinter as PP

import qualified Data.Macaw.AArch32.Symbolic as DMAS
import qualified Data.Macaw.ARM as DMA
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Language.ASL.Globals as ASL
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.CFG.Common as LCCC
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LCLMP
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Types as LCT
import qualified What4.BaseTypes as WT
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
import qualified Stubs.Memory.AArch32.Linux ()
import qualified Stubs.Memory as SM

-- | Integer arguments are passed in the first four registers in ARM. Functions
-- that require additional arguments are passed on the stack at @[sp, #0]@,
-- @[sp, #4]@, etc.
aarch32LinuxIntegerArguments
  :: forall atps sym bak mem
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     )
  => bak
  -> DMS.GenArchVals mem DMA.ARM
  -- ^ ARM-specific architecture information
  -> LCT.CtxRepr atps
  -- ^ The argument types
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes DMA.ARM)
  -- ^ A register structure containing symbolic values
  -> LCLM.MemImpl sym
  -- ^ The memory state at the time of the function call
  -> IO (Ctx.Assignment (LCS.RegEntry sym) atps, AF.GetVarArg sym)
aarch32LinuxIntegerArguments bak archVals argTypes regFile mem = do
  let ?ptrWidth = ptrWidth
  let stackArgList = map (AFS.loadIntegerStackArgument bak archVals regFile mem)
                         [0..]
  let argList = regArgList ++ stackArgList
  AO.buildArgumentAssignment bak argTypes argList
  where
    ptrWidth = PN.knownNat @32
    regArgList = map (pure . lookupReg) aarch32LinuxIntegerArgumentRegisters
    lookupReg r = LCS.RegEntry (LCLM.LLVMPointerRepr ptrWidth)
                               (LCS.unRV (DMAS.lookupReg r regFile))

aarch32LinuxIntegerArgumentRegisters :: [ARMReg.ARMReg (DMT.BVType 32)]
aarch32LinuxIntegerArgumentRegisters =
  [ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
  , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")
  , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")
  , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")
  ]

-- | Inject override return values back into the register state
--
-- Void returns ('LCT.UnitRepr') have no effect.
--
-- Otherwise, an integer return value is placed into r0
aarch32LinuxIntegerReturnRegisters
  :: forall sym bak mem tp p ext r args rtp
   . (LCB.IsSymBackend sym bak)
  => bak
  -> DMS.GenArchVals mem DMA.ARM
  -> LCT.TypeRepr tp
  -> AF.OverrideResult sym DMA.ARM tp
  -> LCS.RegValue sym (DMS.ArchRegStruct DMA.ARM)
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMA.ARM))
aarch32LinuxIntegerReturnRegisters bak _archVals ovTy result initRegs =
  case ovTy of
    LCT.UnitRepr -> do
      return $ updateRegs initRegs
    LCLM.LLVMPointerRepr w
      | Just PC.Refl <- PC.testEquality w (PN.knownNat @32) -> do
          let r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
          return $! updateRegs (DMAS.updateReg r0 (const (LCS.RV (AF.result result))) initRegs)
    LCLM.LLVMPointerRepr w
      | Just PC.Refl <- PC.testEquality w (PN.knownNat @16) -> do
          liftIO $ extendResult result
    LCLM.LLVMPointerRepr w
      | Just PC.Refl <- PC.testEquality w (PN.knownNat @8) -> do
          liftIO $ extendResult result
    _ -> AP.panic AP.FunctionOverride "aarch32LinuxIntegerReturnRegisters" [ "Unsupported return type: " ++ show ovTy ]
  where
    sym = LCB.backendGetSym bak

    -- Zero extend return value to fit in 32-bit register and update register
    -- state.
    extendResult
      :: (1 WI.<= srcW, DMT.KnownNat srcW)
      => AF.OverrideResult sym DMA.ARM (LCLM.LLVMPointerType srcW)
      -> IO (LCS.RegValue sym (DMS.ArchRegStruct DMA.ARM))
    extendResult ovRes = do
      asBv <- LCLM.projectLLVM_bv bak (AF.result ovRes)
      asPtr <- AO.bvToPtr sym asBv (PN.knownNat @32)
      let r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
      return $! updateRegs (DMAS.updateReg r0 (const (LCS.RV asPtr)) initRegs)

    updateRegs regs =
      foldl' (\r (reg, val) -> DMAS.updateReg reg (const (LCS.RV val)) r)
             regs
             (AF.regUpdates result)

-- | Retrieve the return address for the function being called by looking up
-- the current value of the link register.
aarch32LinuxReturnAddr ::
  forall bak mem sym solver scope st fs.
     ( bak ~ LCBO.OnlineBackend solver scope st fs
     , sym ~ WE.ExprBuilder scope st fs
     , LCB.IsSymBackend sym bak
     , WPO.OnlineSolver solver
     )
  => bak
  -> DMS.GenArchVals mem DMA.ARM
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes DMA.ARM)
  -- ^ Registers to extract LR from
  -> LCLM.MemImpl sym
  -- ^ The memory state at the time of the function call
  -> IO (Maybe (DMM.MemWord 32))
aarch32LinuxReturnAddr bak archVals regs _mem = do
  let addrSymBV = LCLMP.llvmPointerOffset $ LCS.regValue
                                          $ DMS.lookupReg archVals regsEntry ARMReg.arm_LR
  res <- AVC.resolveSymBVAs bak WT.knownNat addrSymBV
  case res of
    Left AVC.UnsatInitialAssumptions -> do
      loc <- WI.getCurrentProgramLoc sym
      AP.panic AP.FunctionOverride "aarch32LinuxReturnAddr"
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

    regsEntry :: LCS.RegEntry sym (LCT.StructType (DMS.MacawCrucibleRegTypes DMA.ARM))
    regsEntry = LCS.RegEntry (LCT.StructRepr (DMS.crucArchRegTypes (DMS.archFunctions archVals))) regs

-- | Model @__kuser_get_tls@ by returning the value stored in the TLS global
-- variable. See @Note [AArch32 and TLS]@.
buildKUserGetTLSOverride ::
     LCLM.HasPtrWidth w
  => LCCC.GlobalVar (LCLM.LLVMPointerType w)
     -- ^ Global variable for TLS
  -> AF.FunctionOverride p sym Ctx.EmptyCtx arch (LCLM.LLVMPointerType w)
buildKUserGetTLSOverride tlsGlob =
  PN.withKnownNat ?ptrWidth $
  AF.mkFunctionOverride "__kuser_get_tls" $ \bak args ->
    Ctx.uncurryAssignment (callKUserGetTLSOverride bak tlsGlob) args

callKUserGetTLSOverride ::
     ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth w
     )
  => bak
  -> LCCC.GlobalVar (LCLM.LLVMPointerType w)
     -- ^ Global variable for TLS
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (LCLM.LLVMPointerType w))
callKUserGetTLSOverride _bak tlsGlob = do
  globState <- use (LCSE.stateTree . LCSE.actFrame . LCSE.gpGlobals)
  case LCSG.lookupGlobal tlsGlob globState of
    Nothing -> AP.panic AP.FunctionOverride "callKUserGetTLSOverride"
                 [ "Failed to find global TLS variable: "
                   ++ show (LCCC.globalName tlsGlob) ]
    Just tlsPtr -> pure tlsPtr

aarch32LinuxFunctionABI ::
     (?memOpts :: LCLM.MemOptions, LCLM.HasLLVMAnn sym)
  => LCCC.GlobalVar (LCLM.LLVMPointerType 32)
     -- ^ Global variable for TLS
  -> SM.BuildFunctionABI DMA.ARM sym (AE.AmbientSimulatorState sym DMA.ARM) DMS.LLVMMemory
aarch32LinuxFunctionABI tlsGlob = SM.BuildFunctionABI $ \fovCtx  initialMem archVals unsupportedRelocs addrOvs namedOvs otherGlobs ->
  let ?ptrWidth = PN.knownNat @32 in
  let (nameMap, globMap) = AFC.mkFunctionNameGlobMaps namedOvs
                             otherGlobs [] in
  let customKernelOvs =
        -- The addresses are taken from
        -- https://github.com/torvalds/linux/blob/5bfc75d92efd494db37f5c4c173d3639d4772966/Documentation/arm/kernel_user_helpers.rst
        [ -- __kuser_get_tls (See Note [AArch32 and TLS])
          ( AF.AddrFromKernel 0xffff0fe0
          , AF.SomeFunctionOverride (buildKUserGetTLSOverride tlsGlob) NEL.:| []
          )
        ] in
  SM.FunctionABI { SM.functionIntegerArguments = \bak ->
                     aarch32LinuxIntegerArguments bak archVals
                 , SM.functionIntegerArgumentRegisters = aarch32LinuxIntegerArgumentRegisters
                 , SM.functionIntegerReturnRegisters = aarch32LinuxIntegerReturnRegisters
                 , SM.functionReturnAddr = aarch32LinuxReturnAddr
                 , SM.functionNameMapping = nameMap
                 , SM.functionGlobalMapping = globMap
                 , SM.functionAddrMapping =
                     Map.union (Map.fromList customKernelOvs) addrOvs
                 }

-- | A lookup function from 'AFE.TypeAlias' to types with the appropriate width
-- on Arm32 Linux.
aarch32LinuxTypes :: AFE.TypeLookup
aarch32LinuxTypes = AFE.TypeLookup $ \tp ->
  case tp of
    AFE.Byte -> Some (LCT.BVRepr (PN.knownNat @8))
    AFE.Int -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Long -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.PidT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Pointer -> Some (LCLM.LLVMPointerRepr (PN.knownNat @32))
    AFE.Short -> Some (LCT.BVRepr (PN.knownNat @16))
    AFE.SizeT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.UidT -> Some (LCT.BVRepr (PN.knownNat @32))

{-
Note [AArch32 and TLS]
~~~~~~~~~~~~~~~~~~~~~~
AArch32 handles thread-local state (TLS) in the following ways:

1. The __ARM_NR_set_tls syscall sets the TLS value.
2. The __kuser_get_tls function returns the TLS value. (__kuser_get_tls is a
   special function provided by the Linux kernel—more on this in a bit.)

We do not currently model (1). The _start() function in a glibc-compiled binary
often performs (1), but we do not yet support glibc's implementation of
_start(). See #22.

On the other hand, (2) occurs whenever one invokes the syscall() function in
glibc, as their implementation of syscall() uses TLS for error-handling
purposes. To support this, we do the following:

* When initializing memory in AArch32, we create a global variable representing
  the TLS state and initialize it with a fresh symbolic value. See
  Ambient.Memory.AArch32.Linux.initTLSMemory. This is essentially the same
  approach that is used on the x86_64 side to handle fsbase and gsbase.
  (See Note [x86_64 and TLS] in A.Memory.X86_64.Linux.)

* The Linux kernel provides __kuser_get_tls at a fixed address in the user
  space of all running AArch32 binaries (see aarch32LinuxFunctionABI for the
  specific address). Macaw-loaded binaries do not display this address, but it
  is there nonetheless. To model these special addresses, a FunctionABI has a
  functionKernelAddrMapping that maps fixed kernel function addresses to custom
  overrides. Later in Ambient.Verifier.SymbolicExecution.lookupFunction, the
  functionKernelAddrMapping is consulted first before trying to resolve a
  function address to a function name in a binary.

  (Aside: this is not the only possible way of doing this. Instead of having
  a separate mapping on the side, we could also take the Macaw-loaded binary
  and manually inject the relevant function addresses into its Memory. While
  this would have the benefit of not needing any special cases in
  lookupFunction, it has the downside of being somewhat tricky to implement,
  so we do not take this approach currently.)

* aarch32LinuxFunctionABI defines a custom override for __kuser_get_tls in its
  functionKernelAddrMapping. The override simply returns the value stored in
  the TLS global variable that was initialized earlier. At present, this will
  always return the same symbolic value, but this could change in the future if
  we model the __ARM_NR_set_tls syscall.
-}
