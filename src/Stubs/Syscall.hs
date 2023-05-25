{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module Stubs.Syscall (
    Syscall(..)
  , mkSyscall
  , SomeSyscall(..)
  , SyscallNumRepr(..)
  , SyscallFnHandle(..)
  , SyscallABI(..)
  , BuildSyscallABI(..)
  ) where

import qualified Data.Kind as Kind
import qualified Data.Map.Strict as Map
import qualified Data.IntMap as IM
import qualified Data.Text as DT
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.CFG as DMC
import           Data.Macaw.X86.Symbolic ()
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Protocol.Online as WPO

import qualified Stubs.Memory as AM


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

-------------------------------------------------------------------------------
-- System Call ABI Specification
-------------------------------------------------------------------------------

-- Now we actually need to perform the architecture-specific mapping. We can
-- use the type-level information in the override signatures to help us (and
-- especially the type repr inside of the Syscall type)
--
-- Note that this is data rather than a class because there can be different
-- ABIs for a given architecture (e.g., Windows and Linux)
data SyscallABI arch sym p =
  SyscallABI {
    -- Given a full register state, extract all of the arguments we need for
    -- the system call
    syscallArgumentRegisters
      :: forall bak args atps
       . (LCB.IsSymBackend sym bak)
      => bak
      -> LCT.CtxRepr atps
      -- Types of argument registers
      -> LCS.RegEntry sym (LCT.StructType atps)
      -- Argument register values
      -> LCT.CtxRepr args
      -- Types of syscall arguments
      -> IO (Ctx.Assignment (LCS.RegEntry sym) args)
      -- Syscall argument values

    -- Extract the syscall number from the register state
  , syscallNumberRegister
     :: forall bak atps
      . (LCB.IsSymBackend sym bak)
     => bak
     -> Ctx.Assignment LCT.TypeRepr atps
     -- Types of argument registers
     -> LCS.RegEntry sym (LCT.StructType atps)
     -- Argument register values
     -> IO (LCS.RegEntry sym (LCT.BVType (DMC.ArchAddrWidth arch)))
     -- Extracted syscall number

    -- Build an OverrideSim action with appropriate return register types from
    -- a given OverrideSim action
  , syscallReturnRegisters
     :: forall t ext r args rtps atps
      . LCT.TypeRepr t
     -- Syscall return type
     -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym t)
     -- OverrideSim action producing the syscall's return value
     -> LCT.CtxRepr atps
     -- Argument register types
     -> LCS.RegEntry sym (LCT.StructType atps)
     -- Argument register values from before syscall execution
     -> LCT.CtxRepr rtps
     -- Return register types
     -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym (LCT.StructType rtps))
     -- OverrideSim action with return type matching system return register
     -- type

    -- A mapping from syscall names to overrides
  , syscallOverrideMapping
     :: forall ext
      . ( LCB.IsSymInterface sym
        , LCLM.HasLLVMAnn sym )
     => Map.Map DT.Text (SomeSyscall p sym ext)

    -- A mapping from syscall numbers to names
  , syscallCodeMapping
    :: IM.IntMap DT.Text
  }

-- A function to construct a SyscallABI with file system and memory access, as
-- well as the ability to track whether an 'execve' call has been reached
newtype BuildSyscallABI arch sym p = BuildSyscallABI (
    LCLS.LLVMFileSystem (DMC.ArchAddrWidth arch)
    -- File system to use in syscalls
    -> AM.InitialMemory sym (DMC.ArchAddrWidth arch)
    -> Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch)) String
    -- ^ Mapping from unsupported relocation addresses to the names of the
    -- unsupported relocation types.
    -> SyscallABI arch sym p
  )


