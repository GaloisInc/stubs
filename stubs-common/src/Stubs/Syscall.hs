{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.Syscall (
    Syscall(..)
  , mkSyscall
  , SomeSyscall(..)
  , SyscallNumRepr(..)
  , SyscallFnHandle(..)
  ) where

import qualified Data.Kind as Kind
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Protocol.Online as WPO

-------------------------------------------------------------------------------
-- System Call Overrides
-------------------------------------------------------------------------------

-- | Syscall captures an override and type information about how to call it
data Syscall p sym args ext ret =
  Syscall { syscallName :: WF.FunctionName
          -- ^ Name of the syscall
          , syscallArgTypes :: LCT.CtxRepr args
          -- ^ Types of the arguments to the syscall
          , syscallReturnType :: LCT.TypeRepr ret
          -- ^ Return type of the syscall
          , syscallHasWrapperFunction :: Bool
          -- ^ If 'True', there is also a corresponding wrapper function of the
          -- same name in @libc@ that should use the same override.
          , syscallOverride
              :: forall bak solver scope st fs
               . ( LCB.IsSymBackend sym bak
                 , sym ~ WE.ExprBuilder scope st fs
                 , bak ~ LCBO.OnlineBackend solver scope st fs
                 , WPO.OnlineSolver solver
                 )
              => bak
              -> Ctx.Assignment (LCS.RegEntry sym) args
              -- Arguments to syscall
              -> (forall rtp args' ret'. LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret))
          -- ^ Override capturing behavior of the syscall
          }

-- | A smart constructor for 'Syscall' for the common case when:
--
-- * The argument and result types are statically known.
--
-- * There is a wrapper function of the same name.
mkSyscall ::
  ( LCT.KnownRepr LCT.CtxRepr args
  , LCT.KnownRepr LCT.TypeRepr ret
  ) =>
  WF.FunctionName ->
  (forall bak solver scope st fs
     . ( LCB.IsSymBackend sym bak
       , sym ~ WE.ExprBuilder scope st fs
       , bak ~ LCBO.OnlineBackend solver scope st fs
       , WPO.OnlineSolver solver
       )
    => bak
    -> Ctx.Assignment (LCS.RegEntry sym) args
    -> (forall rtp args' ret'. LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret))) ->
  Syscall p sym args ext ret
mkSyscall name ov = Syscall
  { syscallName = name
  , syscallArgTypes = LCT.knownRepr
  , syscallReturnType = LCT.knownRepr
  , syscallHasWrapperFunction = True
  , syscallOverride = ov
  }

data SomeSyscall p sym ext =
  forall args ret . SomeSyscall (Syscall p sym args ext ret)

-- | A syscall number, paired with the types of the syscall's argument and
-- return registers for the benefit of admitting an 'PC.OrdF' instance.
data SyscallNumRepr :: (Ctx.Ctx LCT.CrucibleType, Ctx.Ctx LCT.CrucibleType) -> Kind.Type where
  SyscallNumRepr :: !(LCT.CtxRepr atps)
                 -> !(LCT.CtxRepr rtps)
                 -> !Integer
                 -> SyscallNumRepr '(atps, rtps)

-- NB: Strictly speaking, this is not a law-abiding TestEquality instance, as
-- testEquality can return Nothing even if the type indices are equal. See the
-- discussion at https://github.com/GaloisInc/parameterized-utils/issues/129.
-- We may want to replace this with an EqF instance in the future should the
-- superclasses of OrdF change.
instance PC.TestEquality SyscallNumRepr where
  testEquality (SyscallNumRepr atps1 rtps1 i1) (SyscallNumRepr atps2 rtps2 i2) = do
    LCT.Refl <- LCT.testEquality atps1 atps2
    LCT.Refl <- LCT.testEquality rtps1 rtps2
    if (i1 == i2) then Just LCT.Refl else Nothing

instance PC.OrdF SyscallNumRepr where
  compareF (SyscallNumRepr atps1 rtps1 i1) (SyscallNumRepr atps2 rtps2 i2) =
    PC.joinOrderingF (PC.compareF atps1 atps2) $
    PC.joinOrderingF (PC.compareF rtps1 rtps2) $
    PC.fromOrdering (compare i1 i2)

instance Show (SyscallNumRepr tps) where
  showsPrec _ (SyscallNumRepr _ _ i) = showString "SyscallNumRepr " . showsPrec 11 i
instance PC.ShowF SyscallNumRepr

-- | A 'LCF.FnHandle' for a syscall override.
data SyscallFnHandle :: (Ctx.Ctx LCT.CrucibleType, Ctx.Ctx LCT.CrucibleType) -> Kind.Type where
  SyscallFnHandle :: !(LCF.FnHandle atps (LCT.StructType rtps))
                  -> SyscallFnHandle '(atps, rtps)

deriving instance Show (SyscallFnHandle tps)
instance PC.ShowF SyscallFnHandle

