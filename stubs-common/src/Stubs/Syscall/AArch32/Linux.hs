{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module defines the mapping from system call numbers to overrides (as
-- well as registers to formal syscall arguments)
--
-- See <https://chromium.googlesource.com/chromiumos/docs/+/master/constants/syscalls.md#arm-32_bit_EABI>
-- for the system call number mapping
module Stubs.Syscall.AArch32.Linux (
  aarch32LinuxSyscallABI
  ) where

import qualified Data.Map as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN

import qualified Data.Macaw.ARM as DMA
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Types as DMT
import qualified Language.ASL.Globals as ASL
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF

import qualified Stubs.Extensions as AE
import qualified Stubs.Override as AO
import qualified Stubs.Panic as AP
import qualified Stubs.Syscall as AS
import qualified Stubs.Syscall.Names.AArch32.Linux as SN
import qualified Stubs.Syscall.Overrides as ASO

type SyscallRegsType = Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 32
                                    Ctx.::> LCLM.LLVMPointerType 32
                                    Ctx.::> LCLM.LLVMPointerType 32
                                    Ctx.::> LCLM.LLVMPointerType 32
                                    Ctx.::> LCLM.LLVMPointerType 32
                                    Ctx.::> LCLM.LLVMPointerType 32
                                    Ctx.::> LCLM.LLVMPointerType 32
                                    Ctx.::> LCLM.LLVMPointerType 32

-- | Arguments are passed in r0-r6. The syscall number is passed in r7.
--
-- All of the syscall functions get the same register struct with all of these
-- registers in order.  We define this repr here so that we can easily test
-- equality. Moreover, testing equality on a single value like 'syscallABIRepr'
-- prevents GHC's pattern-match coverage checker from taking an unreasonable
-- amount of time to finish, which is not the case if you match on each
-- register in its own call to 'PC.testEquality'.
--
-- Recall that the shape of these arguments are determined by the translation
-- from macaw into crucible, which fixes the shape of arguments passed to system
-- call handlers.
syscallABIRepr :: Ctx.Assignment LCT.TypeRepr SyscallRegsType
syscallABIRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)

aarch32LinuxGetReg
  :: Ctx.Assignment LCT.TypeRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> ARMReg.ARMReg (DMT.BVType 32)
  -> LCS.RegValue' sym (LCLM.LLVMPointerType 32)
aarch32LinuxGetReg tps regs reg
  | Just PC.Refl <- PC.testEquality tps syscallABIRepr =
      case LCS.regValue regs of
        Ctx.Empty Ctx.:> r0 Ctx.:> r1 Ctx.:> r2 Ctx.:> r3 Ctx.:> r4 Ctx.:> r5 Ctx.:> r6 Ctx.:> r7 ->
          case reg of
            ARMReg.ARMGlobalBV ref
              | Just PC.Refl <- PC.testEquality ref (ASL.knownGlobalRef @"_R0") -> r0
              | Just PC.Refl <- PC.testEquality ref (ASL.knownGlobalRef @"_R1") -> r1
              | Just PC.Refl <- PC.testEquality ref (ASL.knownGlobalRef @"_R2") -> r2
              | Just PC.Refl <- PC.testEquality ref (ASL.knownGlobalRef @"_R3") -> r3
              | Just PC.Refl <- PC.testEquality ref (ASL.knownGlobalRef @"_R4") -> r4
              | Just PC.Refl <- PC.testEquality ref (ASL.knownGlobalRef @"_R5") -> r5
              | Just PC.Refl <- PC.testEquality ref (ASL.knownGlobalRef @"_R6") -> r6
              | Just PC.Refl <- PC.testEquality ref (ASL.knownGlobalRef @"_R7") -> r7
            _ -> AP.panic AP.Syscall "aarch32LinuxGetReg" ["Unexpected syscall register: " ++ show reg]
  | otherwise = AP.panic AP.Syscall "aarch32LinuxGetReg" [ "Unexpected syscall args shape"
                                                         , " Expected: " ++ show syscallABIRepr
                                                         , " But got: " ++ show tps
                                                         ]


-- | The syscall number is in r7 (see @man 2 syscall@)
aarch32LinuxSyscallNumberRegister
  :: forall sym bak w atps
   . ( LCB.IsSymBackend sym bak
     , w ~ DMC.ArchAddrWidth DMA.ARM
     )
  => bak
  -> Ctx.Assignment LCT.TypeRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> IO (LCS.RegEntry sym (LCT.BVType w))
aarch32LinuxSyscallNumberRegister bak repr regs = do
  bv <- LCLM.projectLLVM_bv bak (LCS.unRV (aarch32LinuxGetReg repr regs r7))
  return LCS.RegEntry { LCS.regType = LCT.BVRepr PN.knownNat
                      , LCS.regValue = bv
                      }
  where
    r7 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R7")

-- | Syscall arguments are passed in (in order): r0, r1, r2, r3, r4, r5, r6
--
-- See @man 2 syscall@
aarch32LinuxSyscallArgumentRegisters
  :: (LCB.IsSymBackend sym bak)
  => bak
  -> LCT.CtxRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> LCT.CtxRepr args
  -> IO (Ctx.Assignment (LCS.RegEntry sym) args)
aarch32LinuxSyscallArgumentRegisters bak regTypes regs syscallTypes
  | Just PC.Refl <- PC.testEquality regTypes syscallABIRepr =
      case LCS.regValue regs of
        Ctx.Empty Ctx.:> r0 Ctx.:> r1 Ctx.:> r2 Ctx.:> r3 Ctx.:> r4 Ctx.:> r5 Ctx.:> r6 Ctx.:> _ -> do
          let regEntries = map (pure . toRegEntry) [r0, r1, r2, r3, r4, r5, r6]
          -- No syscalls make use of variadic arguments (see Note [Varargs] in
          -- Ambient.FunctionOverride), so we do not make use of the GetVarArg
          -- callback.
          (regAssn, _getVarArg) <- AO.buildArgumentAssignment bak syscallTypes regEntries
          pure regAssn
  | otherwise = AP.panic AP.Syscall "aarch32LinuxSyscallArgumentRegisters" [ "Unexpected argument register shape: " ++ show regTypes ]
  where
    ptrWidth = PN.knownNat @32
    toRegEntry x = LCS.RegEntry (LCLM.LLVMPointerRepr ptrWidth) (LCS.unRV x)

type SyscallRetType = Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 32 Ctx.::> LCLM.LLVMPointerType 32

syscallRetRepr :: Ctx.Assignment LCT.TypeRepr SyscallRetType
syscallRetRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32) Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32)

-- | Returned values are in r0 and r1
--
-- NOTE: We just pass r1 through right now and assume that a single integer
-- return value is placed into r0 (or no return if the syscall is void)
aarch32LinuxSyscallReturnRegisters
  :: LCT.TypeRepr tp
  -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym tp)
  -> LCT.CtxRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> LCT.CtxRepr rtps
  -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (Ctx.Assignment (LCS.RegValue' sym) rtps)
aarch32LinuxSyscallReturnRegisters ovTy ovSim argsRepr args retRepr
  | Just PC.Refl <- PC.testEquality retRepr syscallRetRepr =
      case ovTy of
        LCT.UnitRepr -> do
          ovSim
          let r0Val = aarch32LinuxGetReg argsRepr args r0
          let r1Val = aarch32LinuxGetReg argsRepr args r1
          return (Ctx.Empty Ctx.:> r0Val Ctx.:> r1Val)
        LCLM.LLVMPointerRepr w
          | Just PC.Refl <- PC.testEquality w ptrWidth -> do
              result <- ovSim
              let r1Val = aarch32LinuxGetReg argsRepr args r1
              return (Ctx.Empty Ctx.:> LCS.RV result Ctx.:> r1Val)
        _ -> AP.panic AP.Syscall "aarch32LinuxSyscallReturnRegisters" [ "Unexpected override return type: " ++ show ovTy ]
  | otherwise = AP.panic AP.Syscall "aarch32LinuxSyscallReturnRegisters" [ "Unexpected return shape"
                                                                         , " AArch32 handler expected: " ++ show syscallRetRepr
                                                                         , " Call site provided: " ++ show retRepr
                                                                         ]
  where
    ptrWidth = PN.knownNat @32
    r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
    r1 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")

aarch32LinuxSyscallABI :: AS.BuildSyscallABI DMA.ARM sym (AE.AmbientSimulatorState sym DMA.ARM)
aarch32LinuxSyscallABI = AS.BuildSyscallABI $ \fs initialMem unsupportedRelocs ->
  let ?ptrWidth = PN.knownNat @32 in
  AS.SyscallABI { AS.syscallArgumentRegisters = aarch32LinuxSyscallArgumentRegisters
                , AS.syscallNumberRegister = aarch32LinuxSyscallNumberRegister
                , AS.syscallReturnRegisters = aarch32LinuxSyscallReturnRegisters
                , AS.syscallOverrideMapping = Map.fromList
                    [ (WF.functionName (AS.syscallName s), ss)
                    | ss@(AS.SomeSyscall s) <-
                        ASO.allOverrides fs initialMem unsupportedRelocs
                    ]
                , AS.syscallCodeMapping = SN.syscallMap
                }
