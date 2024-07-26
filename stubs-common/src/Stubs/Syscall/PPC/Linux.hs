{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module defines the mapping from PowerPC system call numbers to
-- overrides (as well as registers to formal syscall arguments).
module Stubs.Syscall.PPC.Linux (
    ppcLinuxSyscallArgumentRegisters
  , ppcLinuxSyscallNumberRegister
  , ppcLinuxSyscallReturnRegisters
  , ppcLinuxSyscallABI
  ) where

import Control.Monad.IO.Class (MonadIO(..))
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN

import qualified Data.Macaw.PPC as DMP
import qualified Data.Macaw.Types as DMT
import qualified Dismantle.PPC as D
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified SemMC.Architecture.PPC as SAP
import qualified What4.Interface as WI

import qualified Stubs.Extensions as AE
import qualified Stubs.Override as AO
import qualified Stubs.Panic as AP
import qualified Stubs.Syscall.Names.PPC32.Linux as SN32
import qualified Stubs.Syscall.Names.PPC64.Linux as SN64
import qualified Stubs.Memory as SM

type SyscallRegsType w = Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                      Ctx.::> LCLM.LLVMPointerType w
                                      Ctx.::> LCLM.LLVMPointerType w
                                      Ctx.::> LCLM.LLVMPointerType w
                                      Ctx.::> LCLM.LLVMPointerType w
                                      Ctx.::> LCLM.LLVMPointerType w
                                      Ctx.::> LCLM.LLVMPointerType w
                                      Ctx.::> LCLM.LLVMPointerType w

-- | An register assignment consisting of:
--
-- * The syscall number, which is passed in @r0@.
--
-- * Arguments are passed in @r3@-@r9@ (on PPC32) or @r3-r8@ (on PPC64). For the
-- sake of convenience, we include all of the registers from @r3@-@r9@,
-- regardless of whether PPC32 or PPC64 is used. (The value of @r9@ is unused
-- on PPC64.)
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
syscallABIRepr ::
  (1 PN.<= w) =>
  -- | The register width (@32@ for PPC32 or @64@ for PPC64).
  PN.NatRepr w ->
  Ctx.Assignment LCT.TypeRepr (SyscallRegsType w)
syscallABIRepr w = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr w
                             Ctx.:> LCLM.LLVMPointerRepr w
                             Ctx.:> LCLM.LLVMPointerRepr w
                             Ctx.:> LCLM.LLVMPointerRepr w
                             Ctx.:> LCLM.LLVMPointerRepr w
                             Ctx.:> LCLM.LLVMPointerRepr w
                             Ctx.:> LCLM.LLVMPointerRepr w
                             Ctx.:> LCLM.LLVMPointerRepr w

ppcLinuxGetReg ::
     forall v sym atps
   . DMP.KnownVariant v
  => Ctx.Assignment LCT.TypeRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> DMP.PPCReg v (DMT.BVType (SAP.AddrWidth v))
  -> LCS.RegValue' sym (LCLM.LLVMPointerType (SAP.AddrWidth v))
ppcLinuxGetReg tps regs reg
  | Just PC.Refl <- PC.testEquality tps regsRepr =
      case LCS.regValue regs of
        Ctx.Empty Ctx.:> r0 Ctx.:> r3 Ctx.:> r4 Ctx.:> r5 Ctx.:> r6 Ctx.:> r7 Ctx.:> r8 Ctx.:> r9
          | Just PC.Refl <- PC.testEquality reg (DMP.PPC_GP (D.GPR 0)) -> r0
          | Just PC.Refl <- PC.testEquality reg (DMP.PPC_GP (D.GPR 3)) -> r3
          | Just PC.Refl <- PC.testEquality reg (DMP.PPC_GP (D.GPR 4)) -> r4
          | Just PC.Refl <- PC.testEquality reg (DMP.PPC_GP (D.GPR 5)) -> r5
          | Just PC.Refl <- PC.testEquality reg (DMP.PPC_GP (D.GPR 6)) -> r6
          | Just PC.Refl <- PC.testEquality reg (DMP.PPC_GP (D.GPR 7)) -> r7
          | Just PC.Refl <- PC.testEquality reg (DMP.PPC_GP (D.GPR 8)) -> r8
          | Just PC.Refl <- PC.testEquality reg (DMP.PPC_GP (D.GPR 8)) -> r9
        _ -> AP.panic AP.Syscall "ppcLinuxGetReg" ["Unexpected syscall register: " ++ show reg]
  | otherwise = AP.panic AP.Syscall "ppcLinuxGetReg" [ "Unexpected syscall args shape"
                                                     , " Expected: " ++ show regsRepr
                                                     , " But got: " ++ show tps
                                                     ]
  where
    regsRepr = syscallABIRepr $ SAP.addrWidth $ DMP.knownVariant @v

-- | The syscall number is in r0 (see @man 2 syscall@).
ppcLinuxSyscallNumberRegister ::
     forall v sym bak atps
   . ( LCB.IsSymBackend sym bak
     , DMP.KnownVariant v
     )
  => bak
  -> Ctx.Assignment LCT.TypeRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> IO (LCS.RegEntry sym (LCT.BVType (SAP.AddrWidth v)))
ppcLinuxSyscallNumberRegister bak repr regs = do
  bv <- LCLM.projectLLVM_bv bak (LCS.unRV (ppcLinuxGetReg repr regs r0))
  return LCS.RegEntry { LCS.regType = LCT.BVRepr w
                      , LCS.regValue = bv
                      }
  where
    w = SAP.addrWidth $ DMP.knownVariant @v
    r0 = DMP.PPC_GP (D.GPR 0)

-- | Syscall arguments are passed in:
--
-- * @r3@ through @r9@ (on PPC32)
-- * @r3@ through @r8@ (on PPC64)
--
-- For the sake of convenience, we include all of the registers from @r3@-@r9@,
-- regardless of whether PPC32 or PPC64 is used. (The value of @r9@ is unused
-- on PPC64.)
--
-- See @man 2 syscall@.
ppcLinuxSyscallArgumentRegisters ::
     forall v sym bak atps args
   . ( LCB.IsSymBackend sym bak
     , DMP.KnownVariant v
     )
  => DMP.VariantRepr v
  -> bak
  -> LCT.CtxRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> LCT.CtxRepr args
  -> IO (Ctx.Assignment (LCS.RegEntry sym) args)
ppcLinuxSyscallArgumentRegisters variantRepr bak regTypes regs syscallTypes
  | Just PC.Refl <- PC.testEquality regTypes regsRepr =
      case LCS.regValue regs of
        Ctx.Empty Ctx.:> _r0 Ctx.:> r3 Ctx.:> r4 Ctx.:> r5 Ctx.:> r6 Ctx.:> r7 Ctx.:> r8 Ctx.:> r9 -> do
          let regEntries = map (pure . toRegEntry) [r3, r4, r5, r6, r7, r8, r9]
          -- No syscalls make use of variadic arguments (see Note [Varargs] in
          -- Ambient.FunctionOverride), so we do not make use of the GetVarArg
          -- callback.
          (regAssn, _getVarArg) <- AO.buildArgumentAssignment (LCB.backendGetSym bak) syscallTypes regEntries
          pure regAssn
  | otherwise = AP.panic AP.Syscall "ppcLinuxSyscallArgumentRegisters" [ "Unexpected argument register shape: " ++ show regTypes ]
  where
    ptrWidth = SAP.addrWidth variantRepr
    regsRepr = syscallABIRepr ptrWidth

    toRegEntry :: LCS.RegValue' sym (LCLM.LLVMPointerType (SAP.AddrWidth v))
               -> LCS.RegEntry sym (LCLM.LLVMPointerType (SAP.AddrWidth v))
    toRegEntry x = LCS.RegEntry (LCLM.LLVMPointerRepr ptrWidth) (LCS.unRV x)

-- This is a tuple of form (R0, R3) [on PPC32] or (CR, R3) [on PPC64].
-- Note that this is reversed from the return type of PPCSyscall, which
-- uses the opposite order. This is because Macaw tuples have the order
-- of their fields reversed when converted to a Crucible value (see
-- 'macawListToCrucible' in "Data.Macaw.Symbolic.PersistentState" in
-- @macaw-symbolic@), so we also reverse the order here to be consistent
-- with this convention.
type SyscallRetType w = Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 32 Ctx.::> LCLM.LLVMPointerType w

syscallRetRepr ::
  (1 PN.<= w) => PN.NatRepr w -> Ctx.Assignment LCT.TypeRepr (SyscallRetType w)
syscallRetRepr w = Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr (PN.knownNat @32) Ctx.:> LCLM.LLVMPointerRepr w

-- | PPC syscalls return a value (in @r3@) and an error condition (in @r0@ on
-- PPC32, or in the @cr0.SO@ bit on PPC64). If the error condition is false
-- (i.e., if @r0@ is 0 on PPC32, or if @cr0.SO@ is clear on PPC64), this
-- indicates that the syscall did not error. If the error condition is true
-- (i.e., if @r0@ is -1 on PPC32, or if @cr0.SO@ is set on PPC64), this
-- indicates that the syscall failed and that @r3@ contains an error value,
-- which normally corresponds to @errno@. We always represent the error
-- condition as a full register value, even though only the @cr0.SO@ bit of
-- this value is used on PPC64.
--
-- NOTE: If the return type only contains a single value, we place it in @r3@
-- and assume that the syscall was successful by placing @0@ in @r0@/@cr@.
ppcLinuxSyscallReturnRegisters ::
     forall v p sym ext r args atps rtps tp
   . DMP.KnownVariant v
  => DMP.VariantRepr v
  -> LCT.TypeRepr tp
  -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym tp)
  -> LCT.CtxRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> LCT.CtxRepr rtps
  -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (Ctx.Assignment (LCS.RegValue' sym) rtps)
ppcLinuxSyscallReturnRegisters variantRepr ovTy ovSim argsRepr args retRepr
  | Just PC.Refl <- PC.testEquality retRepr regsRepr =
      case ovTy of
        LCT.UnitRepr -> do
          ovSim
          let r3Val = ppcLinuxGetReg argsRepr args r3
          success <- errorCodeSuccess
          return (Ctx.Empty Ctx.:> success Ctx.:> r3Val)
        LCLM.LLVMPointerRepr w
          | Just PC.Refl <- PC.testEquality w ptrWidth -> do
              result <- ovSim
              success <- errorCodeSuccess
              return (Ctx.Empty Ctx.:> success Ctx.:> LCS.RV result)
        -- In the case below, the user will override a syscall such that it
        -- returns a tuple of (R3, R0) [on PPC32] or (R3, CR) [on PPC64], but
        -- macaw-symbolic expects the opposite order (see the comments above
        -- SyscallRetType).
        LCT.StructRepr (Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr resW Ctx.:> LCLM.LLVMPointerRepr errorCodeW)
          | Just PC.Refl <- PC.testEquality resW ptrWidth
          , Just PC.Refl <- PC.testEquality errorCodeW (PN.knownNat @32) -> do
              (Ctx.Empty Ctx.:> result Ctx.:> errorCode) <- ovSim
              return (Ctx.Empty Ctx.:> errorCode Ctx.:> result)
        _ -> AP.panic AP.Syscall "ppcLinuxSyscallReturnRegisters" [ "Unexpected override return type: " ++ show ovTy ]
  | otherwise = AP.panic AP.Syscall "ppcLinuxSyscallReturnRegisters" [ "Unexpected return shape"
                                                                     , " PPC handler expected: " ++ show regsRepr
                                                                     , " Call site provided: " ++ show retRepr
                                                                     ]
  where
    ptrWidth = SAP.addrWidth variantRepr
    regsRepr = syscallRetRepr ptrWidth

    -- If the user does not explicitly return an error code, assume that the
    -- syscall was successful by setting the error code to 0.
    errorCodeSuccess ::
      LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue' sym (LCLM.LLVMPointerType 32))
    errorCodeSuccess =
      LCS.ovrWithBackend $ \bak -> liftIO $ do
        let sym = LCB.backendGetSym bak
        successBV <- WI.bvZero sym (PN.knownNat @32)
        LCS.RV <$> LCLM.llvmPointer_bv sym successBV

    r3 :: DMP.PPCReg v (DMT.BVType (SAP.AddrWidth v))
    r3 = DMP.PPC_GP (D.GPR 3)

ppcLinuxSyscallABI ::
    forall v sym mem
  . DMP.KnownVariant v
 => SM.BuildSyscallABI (DMP.AnyPPC v) sym (AE.AmbientSimulatorState sym (DMP.AnyPPC v)) mem
ppcLinuxSyscallABI = SM.BuildSyscallABI $ \ _initialMem _unsupportedRelocs ->
  let variant = DMP.knownVariant @v in
  let syscallMap =
        case variant of
          DMP.V32Repr -> SN32.syscallMap
          DMP.V64Repr -> SN64.syscallMap in
  let ?ptrWidth = SAP.addrWidth variant in
  SM.SyscallABI {
                  SM.syscallArgumentRegisters = ppcLinuxSyscallArgumentRegisters variant
                , SM.syscallNumberRegister = ppcLinuxSyscallNumberRegister
                , SM.syscallReturnRegisters = ppcLinuxSyscallReturnRegisters variant
                , SM.syscallOverrideMapping = mempty
                , SM.syscallCodeMapping = syscallMap
                }
