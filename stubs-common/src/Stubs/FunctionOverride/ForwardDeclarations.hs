{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.FunctionOverride.ForwardDeclarations
  ( mkForwardDeclarationOverride
  ) where

import           Control.Monad ( unless )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Data.List.NonEmpty as NEL
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as PC

import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Exception as SE
import qualified Stubs.FunctionOverride as SF
import qualified Stubs.FunctionOverride.ArgumentMapping as SFA
import qualified Stubs.Override as SO

-- | Construct an 'LCS.Override' to use when a forward declaration is invoked
-- from a syntax override. See @Note [Resolving forward declarations]@.
mkForwardDeclarationOverride ::
  forall sym bak arch p ext args ret solver scope st fs.
  ( LCB.IsSymBackend sym bak
  , sym ~ WE.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , ext ~ DMS.MacawExt arch
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  NEL.NonEmpty (SF.SomeFunctionOverride p sym arch) ->
  -- ^ Invoke this override (including parent overrides) when calling the
  -- forward declaration.
  WF.FunctionName ->
  -- ^ The name of the forward declaration.
  LCF.FnHandle args ret ->
  -- ^ The forward declaration's handle.
  LCS.Override p sym ext args ret
  -- ^ A Crucible 'LCS.Override' to use when simulating a call to the forward
  -- declaration.
mkForwardDeclarationOverride bak
  (SF.SomeFunctionOverride resolvedFnOv NEL.:| parents) fwdDecName fwdDecHandle =
    LCS.mkOverride' fwdDecName (LCF.handleReturnType fwdDecHandle) ovSim
  where
    sym = LCB.backendGetSym bak
    fwdDecRetType = SFA.promoteBVToPtr $ LCF.handleReturnType fwdDecHandle

    ovSim ::
      forall r.
      LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym ret)
    ovSim = do
      args0 <- LCS.getOverrideArgs
      -- Step (1)
      args1 <- liftIO $ SFA.buildForwardDecOverrideArgs bak $ LCS.regMap args0
      -- Step (2)
      args2 <- liftIO $ extendToRegisterAssignment (SF.functionArgTypes resolvedFnOv) args1
      -- Step (3)
      res <- SF.functionOverride resolvedFnOv bak args2 dummyGetVarArg parents
      unless (null (SF.regUpdates res)) $
        CMC.throwM $ SE.ForwardDeclarationRegUpdateError fwdDecName
      let resValue = SF.result res
      let resEntry0 = LCS.RegEntry (SF.functionReturnType resolvedFnOv) resValue
      -- Step (4)
      resEntry1 <- liftIO $
        SO.narrowPointerType sym fwdDecRetType resEntry0
      -- Step (5)
      resEntry2 <- liftIO $
        SFA.convertBitvector bak (LCF.handleReturnType fwdDecHandle) resEntry1
      pure $ LCS.regValue resEntry2

    -- | Zero-extend the types (if necessary) of the pointer arguments in a
    -- forward declaration override to match the types used in the resolved
    -- function. This corresponds to step (2) in
    -- @Note [Resolving forward declarations]@.
    --
    -- If there is a mismatch in the number of arguments, we throw an exception
    -- here. It is also possible for there to be mismatches in the types of
    -- individual arguments, but that is checked separately in
    -- 'SO.extendPointerType'.
    extendToRegisterAssignment ::
      forall narrowTps regTps.
      LCT.CtxRepr regTps ->
      Ctx.Assignment (LCS.RegEntry sym) narrowTps ->
      IO (Ctx.Assignment (LCS.RegEntry sym) regTps)
    extendToRegisterAssignment regTys narrowEs = go regTys narrowEs
      where
        go :: forall regTps' narrowTps'.
              LCT.CtxRepr regTps' ->
              Ctx.Assignment (LCS.RegEntry sym) narrowTps' ->
              IO (Ctx.Assignment (LCS.RegEntry sym) regTps')
        go Ctx.Empty Ctx.Empty = pure Ctx.Empty
        go (regTypeReprs Ctx.:> regTypeRepr) (narrowEntries Ctx.:> narrowEntry) = do
          regEntry <- SO.extendPointerType sym regTypeRepr narrowEntry
          regEntries <- go regTypeReprs narrowEntries
          pure (regEntries Ctx.:> regEntry)
        go _ _ = CMC.throwM $ SE.ForwardDeclarationArgumentNumberMismatch
                                fwdDecName regTys narrowTys

        narrowTys = PC.fmapFC LCS.regType narrowEs

    -- Syntax overrides do not have a mechanism for variadic arguments—see
    -- Note [Varargs] in Stubs.FunctionOverride. We do permit forward
    -- declarations to refer to variadic functions, but with the caveat that
    -- they are not allowed to make use of variadic functions. For example,
    -- a forward declaration to sprintf with two arguments is acceptable, but
    -- a foward declaration to sprintf with more than two arguments is a type
    -- error.
    --
    -- Still, a crafty user could try to invoke sprintf with a \"%d\" format
    -- string and no other arguments, which would still cause the built-in
    -- sprintf override to invoke its GetVarArg function. Anticipating this
    -- scenario, the dummy GetVarArg callback below simply throws an exception
    -- when it is invoked to cast shame in the user's direction.
    dummyGetVarArg :: SF.GetVarArg sym
    dummyGetVarArg = SF.GetVarArg $ \_ -> CMC.throwM $
      SE.ForwardDeclarationVarArgError fwdDecName

{-
Note [Resolving forward declarations]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Forward declarations are surprisingly tricky to get right. After parsing a
syntax override file containing forward declarations, we must take each
declaration's `Handle` (stored in the `functionForwardDeclarations` field of
the `FunctionOverride` and register it to an appropriate `Override`. Let's use
this as a running example:

  (defun @foo ((x (Bitvector 8))) (Bitvector 8)
    (start start:
      (let res (funcall @bar x))
      (return res)))

  (declare @bar ((x (Bitvector 8))) (Bitvector 8))

When the simulator invokes @bar from @foo, it has an argument of (Bitvector 8)
in hand. But the corresponding override for @bar will _not_ have (Bitvector 8)
as its argument type. The actual argument type depends on what kind of override
is provided for @bar:

* If @bar is another syntax override, then the corresponding `Override` will
  have an `LLVMPointerType 8` argument, due to the pipe-fitting code used in
  stubs-wrapper:Stubs.Wrapper.acfgToFunctionOverride. See
  Note [Bitvector Argument Mapping] in Stubs.FunctionOverride.ArgumentMapping.

* If @bar is a built-in Haskell override, then the corresponding `Override`
  will have an `LLVMPointerType ?ptrWidth` argument by convention.

Either way, we will have to perform some type conversions for the arguments,
and similarly for the result. We proceed as follows:

1. First, convert the (Bitvector 8) argument to an `LLVMPointer 8` using
   Stubs.FunctionOverride.ArgumentMapping.buildForwardDecOverrideArgs.

2. Next, zero-extend the `LLVMPointer 8` argument if necessary using
   `extendToRegisterAssignment`. If @bar is another syntax override, this is a
   no-op, but if @bar is a Haskell override, then this will zero-extend the
   argument to be of type `LLVMPointer ?ptrWidth`.

3. Now that the argument type matches the override for @bar, invoke the
   override.

4. Next, take the result and truncate it if necessary using
   Stubs.Override.narrowPointerType. If @bar is another syntax override, this is
   a no-op but if @bar is a Haskell override, then this will truncate the
   argument from an `LLVMPointer ?ptrWidth` to an `LLVMPointer 8`.

5. Finally, convert the `LLVMPointer 8`-typed result to a (Bitvector 8)
   using Stubs.FunctionOverride.ArgumentMapping.convertBitvector.

This process bears a resemblance to the pipe-fitting code used to implement
`functionIntegerArguments` and `functionIntegerReturnRegisters` in a
FunctionABI, but the pipe-fitting used for forward declarations does not have
to worry about explicitly passing values to/from `macaw` register structs.
(At the moment, forward declarations cannot be used to invoke functions defined
in binaries, which is how we are able to get away with not caring about
register structs for forward declarations.)
-}
