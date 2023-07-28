{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Stubs.Memory (
   InitialMemory(..)
  , MemoryModel(..)
  , memoryModelParser
  , IsStubsMemoryModel(..)
  , ToPtrTy
  , buildRecordLLVMAnnotation
  , MemoryState
  , PtrVal
  , MainArgVals(..)
  , FunctionABI(..)
  , SyscallABI(..)
  , BuildFunctionABI(..)
  , BuildSyscallABI(..)
  ) where

import qualified Control.Applicative as App
import qualified Data.Aeson as DA
import qualified Data.Text as DT
import           Data.Void ( Void )
import qualified Text.Megaparsec as TM
import qualified Text.Megaparsec.Char as TMC

import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.GlobalState as LCSG

import qualified Lang.Crucible.Types as LCT
import GHC.TypeLits
import qualified Stubs.Common as SC
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Parameterized.NatRepr as PN
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Data.Map as Map
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.Partial as LCLMP
import qualified Lang.Crucible.LLVM.Errors as LCLE
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel.CallStack as LCLMC
import Data.IORef (IORef, newIORef, modifyIORef')
import Control.Monad.IO.Class (liftIO, MonadIO)
import qualified Data.Macaw.CFG as DMS
import qualified What4.Interface as WI
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Stubs.Loader.BinaryConfig as SLB
import Data.Parameterized (Some)
import qualified Data.List.NonEmpty as NEL
import Stubs.FunctionOverride
import qualified Data.Parameterized.Context as Ctx
import qualified What4.Protocol.Online as WPO
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified What4.Expr as WE
import qualified Data.Macaw.Types as DMT
import qualified Data.Macaw.CFG as DMC
import qualified What4.FunctionName as WF
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Data.IntMap as IM
import Stubs.Syscall
import qualified Data.Macaw.BinaryLoader as DMB

type family ToPtrTy (tp::LCT.CrucibleType) mem arch :: LCT.CrucibleType where
    ToPtrTy (LCT.BVType w) mem arch = BVToPtrTy w mem arch
    ToPtrTy ty mem arch = ty

type MemoryState sym mem arch = LCS.RegValue sym (MemType mem arch)
type PtrVal sym mem arch = LCS.RegValue sym (PtrType mem arch)

data MainArgVals sym mem arch w = (IsStubsMemoryModel mem arch) => MainArgVals
  { argcVal :: WI.SymBV sym w
  , argvVal :: PtrVal sym mem arch
  , envpVal :: PtrVal sym mem arch
  }

-- | Core typeclass for memory model implementations 
-- In order to have a more reusable simulation pipeline, this typeclass defines core requirements of a memory model
-- NOTE: This abstraction was initially built from code that used LLVMMemory explicitly, so in future some tweaks may be necessary to support 
-- significantly different models.
class (DMS.IsMemoryModel mem, DMS.SymArchConstraints arch) => IsStubsMemoryModel mem arch where
  type PtrType mem arch :: LCT.CrucibleType
  type MemType mem arch :: LCT.CrucibleType
  ptrRepr :: LCT.TypeRepr (PtrType mem arch)
  type family BVToPtrTy (w::Nat) mem arch :: LCT.CrucibleType
  type MemTable sym mem arch
  type MemMap sym arch
  type VerifierState sym mem arch --todo better name

  bvToPtr :: LCT.TypeRepr tp -> LCT.TypeRepr (ToPtrTy tp mem arch)
  memPtrSize :: PN.NatRepr (DMS.ArchAddrWidth arch)
  initMem :: SC.Sym sym -> DMA.ArchitectureInfo arch -> Integer -> SLB.BinaryConfig arch binfmt-> LCF.HandleAllocator -> (Monad m, MonadIO m) => m (InitialMemory sym mem arch) -- meant to replace initializeMemory in symbolic exec
  -- how to get sp from base pointer
  genStackPtr :: (Monad m, MonadIO m) => PtrVal sym mem arch -> WI.SymBV sym (DMS.ArchAddrWidth arch)-> SC.Sym sym -> m (PtrVal sym mem arch)

  insertStackPtr :: (WI.IsExprBuilder sym, LCB.IsSymInterface sym) => DMS.GenArchVals mem arch -> PtrVal sym mem arch -> LCS.RegEntry sym (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))) ->LCS.RegEntry sym (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))

  -- ExtensionImpl defines how to handle Macaw memory operations
  genExtImpl :: (DMB.BinaryLoader
                      arch binfmt, Monad m, MonadIO m) => SC.Sym sym-> InitialMemory sym mem arch 
    -> DMS.MacawArchEvalFn (VerifierState sym mem arch) sym (MemType mem arch) arch 
    -> LCF.HandleAllocator
    -> DMS.GenArchVals mem arch
    -> DMA.ArchitectureInfo arch
    -> SLB.BinaryConfig arch binfmt
    -> FunctionABI arch sym (VerifierState sym mem arch) mem 
    -> SyscallABI arch sym (VerifierState sym mem arch)
    -- -> DMS.LookupFunctionHandle p sym arch -- ties to LLVM :(
    -- -> DMS.LookupSyscallHandle p sym arch
    -> m (LCSE.ExtensionImpl (VerifierState sym mem arch) sym (DMS.MacawExt arch))
  -- ^ implementation of macaw extensions

-- | Initial memory state for symbolic execution
data (IsStubsMemoryModel mem arch) => InitialMemory sym mem arch =
  InitialMemory { imMemVar :: LCS.GlobalVar (MemType mem arch)
               -- ^ MemVar to use in simulation
                , imGlobals :: LCSG.SymGlobalState sym
               -- ^ Initial global variables
                , imStackBasePtr :: LCS.RegValue sym (PtrType mem arch)
               -- ^ Stack memory base pointer 
                , imMemTable :: MemTable sym mem arch
                , imGlobalMap :: MemMap sym arch
                }

-- A function to construct a FunctionABI with memory access
data BuildFunctionABI arch sym p mem = (IsStubsMemoryModel mem arch) => BuildFunctionABI (FunctionOverrideContext arch sym
    -- In what context are the function overrides are being run?
    -- File system to use in overrides
    -> InitialMemory sym mem arch
    -> DMS.GenArchVals mem arch
    -- Architecture-specific information
    -> Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch)) String
    -- ^ Mapping from unsupported relocation addresses to the names of the
    -- unsupported relocation types.
    -> Map.Map (FunctionAddrLoc (DMS.ArchAddrWidth arch))
               (NEL.NonEmpty (SomeFunctionOverride p sym arch))
    -- Overrides for functions at particular addresses
    -> [ SomeFunctionOverride p sym arch ]
    -- Overrides for functions with particular names
    -> [ Some LCS.GlobalVar ]
    -- Additional global variables to register for simulation
    -> FunctionABI arch sym p mem
  )
-------------------------------------------------------------------------------
-- Function Call ABI Specification
-------------------------------------------------------------------------------

-- Now we actually need to perform the architecture-specific mapping. We can
-- use the type-level information in the override signatures to help us (and
-- especially the type repr inside of the FunctionCall type)
--
-- Note that this is data rather than a class because there can be different
-- ABIs for a given architecture (e.g., Windows and Linux)
data FunctionABI arch sym p mem =
  (IsStubsMemoryModel mem arch) =>
  FunctionABI {
    -- Given a full register state, extract all of the arguments we need for
    -- the function call. See Note [Passing arguments to functions].
    functionIntegerArguments
      :: forall bak atps
       . LCB.IsSymBackend sym bak
      => bak
      -> LCT.CtxRepr atps
      -- Types of arguments
      -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
      -- Argument register values
      -> MemoryState sym mem arch
      -- The memory state at the time of the function call
      -> IO (Ctx.Assignment (LCS.RegEntry sym) atps, GetVarArg sym)
      -- A pair containing the function argument values and a callback for
      -- retrieving variadic arguments.

    -- The registers used to pass integer arguments to functions.
  , functionIntegerArgumentRegisters
      :: [DMC.ArchReg arch (DMT.BVType (DMC.ArchAddrWidth arch))]

    -- Build an OverrideSim action with appropriate return register types from
    -- a given OverrideSim action
  , functionIntegerReturnRegisters
     :: forall bak t r args rtp
      . LCB.IsSymBackend sym bak
     => bak
     -> DMS.GenArchVals mem arch
     -- Architecture-specific information
     -> LCT.TypeRepr t
     -- Function return type
     -> OverrideResult sym arch t
     -- Function's return value
     -> LCS.RegValue sym (DMS.ArchRegStruct arch)
     -- Argument register values from before function execution
     -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym (DMS.ArchRegStruct arch))
     -- OverrideSim action with return type matching system return register
     -- type

    -- If the return address for the function being called can be determined,
    -- then return Just that address. Otherwise, return Nothing. Some ABIs
    -- store this information directly in a register, while other ABIs store
    -- this information on the stack, so we provide both registers and the stack
    -- as arguments.
  , functionReturnAddr
      :: forall bak solver scope st fs
       . ( LCB.IsSymBackend sym bak
         , sym ~ WE.ExprBuilder scope st fs
         , bak ~ LCBO.OnlineBackend solver scope st fs
         , WPO.OnlineSolver solver
         )
      => bak
      -> DMS.GenArchVals mem arch
      -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
      -- Registers for the given architecture
      -> MemoryState sym mem arch
      -- The memory state at the time of the function call
      -> IO (Maybe (DMC.MemWord (DMS.ArchAddrWidth arch)))

    -- A mapping of function addresses to overrides. This is utilized for two
    -- purposes:
    --
    -- * User-provided overrides at particular addresses, as specified in an
    --   @overrides.yaml@ file.
    --
    -- * Kernel-provided user helpers that are reachable from user space
    --   at fixed addresses in kernel memory. In particular, see
    --   Note [AArch32 and TLS] in Ambient.FunctionOverride.AArch32.Linux for
    --   how this is used to implement TLS for AArch32 binaries.
    --
    -- Note that if a function's address has an override in this map, that will
    -- always take precedence over any overrides for functions of the same name
    -- in 'functionNameMapping'.  The values of the mapping are nonempty lists
    -- to ensure that at least one override actually exists for each key in the
    -- map.
    --
    -- See @Note [NonEmpty List Override Mapping Values]@ for information on
    -- why the values for the mapping are nonempty lists.
  , functionAddrMapping
     :: Map.Map (FunctionAddrLoc (DMC.ArchAddrWidth arch))
                (NEL.NonEmpty (SomeFunctionOverride p sym arch))

    -- A mapping from function names to overrides.
    --
    -- See @Note [NonEmpty List Override Mapping Values]@ for information on
    -- why the values for the mapping are nonempty lists.
  , functionNameMapping
     :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
     => Map.Map WF.FunctionName
                (NEL.NonEmpty (SomeFunctionOverride p sym arch))

    -- A mapping from global names to global variables.
  , functionGlobalMapping
     :: Map.Map LCSA.GlobalName (Some LCS.GlobalVar)
  }


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
newtype BuildSyscallABI arch sym p mem = BuildSyscallABI (
    InitialMemory sym mem arch
    -> Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch)) String
    -- ^ Mapping from unsupported relocation addresses to the names of the
    -- unsupported relocation types.
    -> SyscallABI arch sym p
  )

-- | Build an LLVM annotation tracker to record instances of bad behavior
-- checks.  Bad behavior encompasses both undefined behavior, and memory
-- errors.  This function returns a function to set '?recordLLVMAnnotation' to,
-- as well as a reference to the record of bad behaviors that will be built up.
buildRecordLLVMAnnotation
  :: LCB.IsSymInterface sym
  => IO ( LCLMC.CallStack -> LCLMP.BoolAnn sym -> LCLE.BadBehavior sym -> IO ()
        , IORef (LCLM.LLVMAnnMap sym) )
buildRecordLLVMAnnotation = do
  badBehavior <- liftIO $ newIORef Map.empty
  let recordFn cs ann behavior = modifyIORef' badBehavior (Map.insert ann (cs, behavior))
  return (recordFn , badBehavior)

-- -- | Initial memory state for symbolic execution
-- data InitialMemory sym w =
--   InitialMemory { imMemModel :: MemoryModel (LCS.GlobalVar (LCLM.LLVMPointerType w))
--                -- ^ Which memory model configuration to use
--                 , imMemVar :: LCS.GlobalVar LCLM.Mem
--                -- ^ MemVar to use in simulation
--                 , imGlobals :: LCSG.SymGlobalState sym
--                -- ^ Initial global variables
--                 , imStackBasePtr :: LCLM.LLVMPtr sym w
--                -- ^ Stack memory base pointer
--                 , imValidityCheck :: DMS.MkGlobalPointerValidityAssertion sym w
--                -- ^ Additional pointer validity checks to enforce
--                 , imGlobalMap :: DMS.GlobalMap sym LCLM.Mem w
--                -- ^ Globals used by the macaw translation; note that this is
--                -- separate from the global variable map passed to crucible, as
--                -- it is only used for initializing the macaw extension
--                 , imMemPtrTable :: AEM.MemPtrTable sym w
--                -- ^ The global memory
--                 }

-- | The memory model configuration. The type of @endVar@ will depend on what
-- part of the verifier we are in:
--
-- * @endVar@ is @()@ if we are parsing a memory model from the command line.
--
-- * @endVar@ is @'LCS.GlobalVar' ('LCLM.LLVMPointerType' w)@ (representing a
--   global variable pointing to the end of the heap) after initializing
--   memory.
data MemoryModel endVar
  = DefaultMemoryModel
    -- ^ The default memory model. All calls to @malloc@/@calloc@ allocate
    --   single, contiguous chunks of memory.
  | BumpAllocator endVar
    -- ^ A bump-allocator–based memory model. The entire heap is represented
    --   with a single allocation, and @endVar@ points to the end of the
    --   allocation. Calls to @malloc@/@calloc@ hand out unused parts of the
    --   heap and bump @endVar@.
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

instance (endVar ~ ()) => DA.FromJSON (MemoryModel endVar) where
  parseJSON = DA.withText "MemoryModel" $ \t ->
    case TM.parse memoryModelParser "" t of
      Left err -> fail $ "Could not parse memory model configuration: "
                      ++ TM.errorBundlePretty err
      Right r  -> pure r

-- | A @megaparsec@ parser for 'MemoryModel's.
memoryModelParser :: TM.Parsec Void DT.Text (MemoryModel ())
memoryModelParser =
  (DefaultMemoryModel <$ TMC.string "default") App.<|>
  (BumpAllocator () <$ TMC.string "bump-allocator")
