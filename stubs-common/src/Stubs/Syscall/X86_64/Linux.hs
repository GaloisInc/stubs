{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.Syscall.X86_64.Linux ( x86_64LinuxSyscallABI ) where

import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Types as DMT
import qualified Data.Macaw.X86 as DMX
import qualified Data.Macaw.X86.X86Reg as DMXR
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI

import qualified Stubs.Extensions as AE
import qualified Stubs.Override as AO
import qualified Stubs.Panic as AP
import qualified Stubs.Syscall as AS
import qualified Stubs.Syscall.Names.X86_64.Linux as SN
import qualified Stubs.Memory as SM

type SyscallRegsType = Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                    Ctx.::> LCLM.LLVMPointerType 64
                                    Ctx.::> LCLM.LLVMPointerType 64
                                    Ctx.::> LCLM.LLVMPointerType 64
                                    Ctx.::> LCLM.LLVMPointerType 64
                                    Ctx.::> LCLM.LLVMPointerType 64
                                    Ctx.::> LCLM.LLVMPointerType 64

-- | Arguments are passed in %rdi, %rsi, %rdx, %r10, %r8, and %r9.
-- The syscall number is passed in %rax.
--
-- All of the syscall functions get the same register struct with all of these
-- registers in order.  We define this repr here so that we can easily test
-- equality. Moreover, testing equality on a single value like 'syscallABIRepr'
-- prevents GHC's pattern-match coverage checker from taking an unreasonable
-- amount of time to finish, which is not the case if you match on each
-- register in its own call to 'WI.testEquality'.
--
-- Recall that the shape of these arguments are determined by the translation
-- from macaw into crucible, which fixes the shape of arguments passed to system
-- call handlers.
syscallABIRepr :: Ctx.Assignment LCT.TypeRepr SyscallRegsType
syscallABIRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @64)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @64)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @64)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @64)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @64)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @64)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @64)

-- | Extract syscall arguments from x86_64 registers.  See documentation on
-- 'syscallArgumentRegisters' for more info.
x86_64LinuxSyscallArgumentRegisters :: forall sym bak args atps
   . ( LCB.IsSymBackend sym bak )
  => bak
  -> LCT.CtxRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> LCT.CtxRepr args
  -> IO (Ctx.Assignment (LCS.RegEntry sym) args)
x86_64LinuxSyscallArgumentRegisters bak regTyps regs syscallTyps
  | Just WI.Refl <- WI.testEquality regTyps syscallABIRepr
  = case LCS.regValue regs of
      Ctx.Empty Ctx.:> _
                Ctx.:> rdi
                Ctx.:> rsi
                Ctx.:> rdx
                Ctx.:> r10
                Ctx.:> r8
                Ctx.:> r9 -> do
        -- Extract argument registers and put in list.
        let regEntries = map (pure . toRegEntry) [rdi, rsi, rdx, r10, r8, r9]
        -- Build an assignment from 'regEntries'
        (regAssn, _) <- AO.buildArgumentAssignment bak syscallTyps regEntries
        -- No syscalls make use of variadic arguments (see Note [Varargs] in
        -- Ambient.FunctionOverride), so we do not make use of the GetVarArg
        -- callback.
        pure regAssn
  | otherwise
  = AP.panic AP.Syscall
             "x86_64LinuxSyscallArgumentRegisters"
             [ "Unexpected argument register shape: " ++ show regTyps ]
  where
    toRegEntry :: LCS.RegValue' sym (LCLM.LLVMPointerType 64)
               -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
    toRegEntry x = (LCS.RegEntry (LCLM.LLVMPointerRepr (WI.knownNat @64)) (LCS.unRV x))

-- | Extract syscall number from x86_64 registers.  See documentation on
-- 'syscallNumberRegister' for more info.
x86_64LinuxSyscallNumberRegister :: forall sym bak w atps
   . ( LCB.IsSymBackend sym bak
     , DMC.RegAddrWidth (DMC.ArchReg DMX.X86_64) ~ w )
  => bak
  -> Ctx.Assignment LCT.TypeRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> IO (LCS.RegEntry sym (LCT.BVType w))
x86_64LinuxSyscallNumberRegister bak typs regs = do
  bv <- LCLM.projectLLVM_bv bak (LCS.unRV (x86_64LinuxGetReg typs regs DMX.RAX))
  return LCS.RegEntry { LCS.regType = LCT.BVRepr WI.knownNat
                      , LCS.regValue = bv }

type SyscallRetType = Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                   Ctx.::> LCLM.LLVMPointerType 64

syscallRetRepr :: Ctx.Assignment LCT.TypeRepr SyscallRetType
syscallRetRepr = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @64)
                           Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @64)

-- | Assemble x86_64 return register state from syscall return value.  See
-- documentation for 'syscallReturnRegisters' for more info.
x86_64LinuxSyscallReturnRegisters
  :: LCT.TypeRepr t
  -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym t)
  -> LCT.CtxRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> LCT.CtxRepr rtps
  -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym (LCT.StructType rtps))
x86_64LinuxSyscallReturnRegisters ovTyp ovSim atps argRegs rtps
  | Just WI.Refl <- WI.testEquality rtps syscallRetRepr
  = case ovTyp of
      LCT.UnitRepr -> do
        ovSim
        let rax = x86_64LinuxGetReg atps argRegs DMXR.RAX
        let rdx = x86_64LinuxGetReg atps argRegs DMXR.RDX
        return (Ctx.empty Ctx.:> rax Ctx.:> rdx)
      LCLM.LLVMPointerRepr w
        | Just WI.Refl <- WI.testEquality w (WI.knownNat @64) -> do
        result <- ovSim
        let rdx = x86_64LinuxGetReg atps argRegs DMXR.RDX
        return (Ctx.empty Ctx.:> (LCS.RV result) Ctx.:> rdx)
      _ -> AP.panic AP.Syscall
                    "x86_64LinuxSyscallReturnRegisters"
                    ["Unsupported override return type"]
      -- NOTE: Fill in return types as needed for new syscall overrides
      -- here
  | otherwise
  = AP.panic AP.Syscall
             "x86_64LinuxSyscallReturnRegisters"
             [ "Unexpected shape of return registers: " ++ show rtps ]

-- | An ABI for Linux syscalls on x86_64 processors
x86_64LinuxSyscallABI :: SM.BuildSyscallABI DMX.X86_64 sym (AE.AmbientSimulatorState sym DMX.X86_64) mem
x86_64LinuxSyscallABI = SM.BuildSyscallABI $ \initialMem unsupportedRelocs ->
  let ?ptrWidth = PN.knownNat @64 in
  SM.SyscallABI { SM.syscallArgumentRegisters = x86_64LinuxSyscallArgumentRegisters
                , SM.syscallNumberRegister = x86_64LinuxSyscallNumberRegister
                , SM.syscallReturnRegisters = x86_64LinuxSyscallReturnRegisters
                , SM.syscallOverrideMapping = mempty
                , SM.syscallCodeMapping = SN.syscallMap
                }

-- | Extract the value of a given register from the x86_64 argument register
-- state
x86_64LinuxGetReg :: Ctx.Assignment LCT.TypeRepr atps
                  -- ^ Types of argument registers
                  -> LCS.RegEntry sym (LCT.StructType atps)
                  -- ^ Argument register state
                  -> DMXR.X86Reg (DMT.BVType 64)
                  -- ^ Register to extract the value from
                  -> LCS.RegValue' sym (LCLM.LLVMPointerType 64)
x86_64LinuxGetReg atps regs reg
  | Just WI.Refl <- WI.testEquality atps syscallABIRepr
  = case LCS.regValue regs of
      Ctx.Empty Ctx.:> rax
                Ctx.:> rdi
                Ctx.:> rsi
                Ctx.:> rdx
                Ctx.:> r10
                Ctx.:> r8
                Ctx.:> r9 ->
        case reg of
          DMXR.RAX -> rax
          DMXR.RDI -> rdi
          DMXR.RSI -> rsi
          DMXR.RDX -> rdx
          DMXR.R10 -> r10
          DMXR.R8  -> r8
          DMXR.R9  -> r9
          _ -> AP.panic AP.Syscall
                       "x86_64LinuxGetReg"
                       ["Unexpected argument register: " ++ (show reg)]
  | otherwise
  = AP.panic AP.Syscall
             "x86_64LinuxGetReg"
             [ "Unexpected argument register shape" ++ show atps ]
