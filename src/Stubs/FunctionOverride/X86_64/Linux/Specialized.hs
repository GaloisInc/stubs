{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | This module provides definitions for overrides specialized for x86_64
-- Linux.

module Stubs.FunctionOverride.X86_64.Linux.Specialized (
    x86_64LinuxSpecializedOverrides
  , x86_64LinuxSprintfOverride
  , x86_64LinuxCallSprintf
  ) where

import           Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.X86 as DMX
import qualified Data.Macaw.X86.X86Reg as DMXR
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Extensions as AExt
import qualified Stubs.FunctionOverride as AF
import qualified Stubs.Panic as AP

-- | All of the overrides specialized for x86_64 Linux.
x86_64LinuxSpecializedOverrides ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ 64
  , ?memOpts :: LCLM.MemOptions
  ) =>
  [ AF.SomeFunctionOverride (AExt.AmbientSimulatorState sym DMX.X86_64)
                            sym
                            DMX.X86_64 ]
x86_64LinuxSpecializedOverrides =
  [ AF.SomeFunctionOverride x86_64LinuxSprintfOverride ]

-- | Specialization function for the musl implementation of @sprintf@.  Updates
-- %rdi to hold a pointer to the end of the output buffer.
--
-- NOTE: This override captures an unintended side effect on machine state.
-- Neither the ABI nor the @sprintf@ specification put any requirements on the
-- value of %rdi (a caller saved register) after execution of @sprintf@.
-- However, we capture this behavior because this side effect would be visible
-- if we were executing the actual machine code.  This behavior may not be
-- stable across different Libc versions or implementations.
x86_64LinuxCallSprintf
  :: ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth 64
     , WPO.OnlineSolver solver
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs )
  => bak
  -> Ctx.Assignment (LCS.RegEntry sym)
                    (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                  Ctx.::> LCLM.LLVMPointerType 64)
  -- ^ The non-variadic arguments, consisting of (1) the output pointer, and
  -- (2) the format string
  -> AF.GetVarArg sym
  -- Variadic arguments to function
  -> [ AF.SomeFunctionOverride p sym DMX.X86_64 ]
  -- ^ Parent overrides
  -> (forall r args ret. LCS.OverrideSim p sym (DMS.MacawExt DMX.X86_64) r args ret (AF.OverrideResult sym DMX.X86_64 (LCLM.LLVMPointerType 64)))
x86_64LinuxCallSprintf bak args varArgs parents = do
  let Ctx.Empty Ctx.:> outPtr Ctx.:> _ = args
  case parents of
    AF.SomeFunctionOverride parent : parents' ->
      case AF.functionArgTypes parent of
        Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr w1 Ctx.:> LCLM.LLVMPointerRepr w2
          | Just WI.Refl <- WI.testEquality w1 (WI.knownNat @64)
          , Just WI.Refl <- WI.testEquality w2 (WI.knownNat @64) ->
          case AF.functionReturnType parent of
            LCLM.LLVMPointerRepr wret
              | Just WI.Refl <- WI.testEquality wret (WI.knownNat @64) -> do
                pRes <- AF.functionOverride parent bak args varArgs parents'
                sizeBv <- liftIO $ LCLM.projectLLVM_bv bak (AF.result pRes)
                rdiVal <- liftIO $ LCLM.ptrAdd sym ?ptrWidth (LCS.regValue outPtr) sizeBv

                -- Return updated register state with new %rdi value.
                return $ pRes { AF.regUpdates = (DMXR.RDI, rdiVal) : (AF.regUpdates pRes) }
            _ -> AP.panic AP.FunctionOverride
                          "x86_64LinuxCallSprintf"
                          ["Parent override has different return type"]
        _ -> AP.panic AP.FunctionOverride
                      "x86_64LinuxCallSprintf"
                      ["Parent override has different argument types"]
    [] ->
      AP.panic AP.FunctionOverride
               "x86_64LinuxCallSprintf"
               ["Tried to invoke parent override, but parents list was empty"]
  where
    sym = LCB.backendGetSym bak

x86_64LinuxSprintfOverride
  :: ( DMC.MemWidth w
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , p ~ AExt.AmbientSimulatorState sym DMX.X86_64
     , w ~ 64
     )
  => AF.FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                             Ctx.::> LCLM.LLVMPointerType w)
                               DMX.X86_64
                               (LCLM.LLVMPointerType w)
x86_64LinuxSprintfOverride =
  AF.mkVariadicSpecializedFunctionOverride "sprintf" x86_64LinuxCallSprintf
