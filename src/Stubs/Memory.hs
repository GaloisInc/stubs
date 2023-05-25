{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Stubs.Memory (
    InitArchSpecificGlobals(..)
  , InitialMemory(..)
  , MemoryModel(..)
  , memoryModelParser
  ) where

import qualified Control.Applicative as App
import qualified Data.Aeson as DA
import qualified Data.Text as DT
import           Data.Void ( Void )
import qualified Text.Megaparsec as TM
import qualified Text.Megaparsec.Char as TMC

import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.GlobalState as LCSG

import qualified Stubs.Extensions.Memory as AEM

-- | 'InitArchSpecificGlobals' provides a function signature for initialization
-- of global variables that are only present on certain architectures or
-- operating systems (e.g., FSBASE on x86).
--
-- It takes an initial 'LCMC.MemImpl' and modifies it as necessary, also
-- returning any auxiliary global variables to support the changes.
newtype InitArchSpecificGlobals arch =
  InitArchSpecificGlobals (  forall sym bak
                             .  ( LCLM.HasLLVMAnn sym
                                , LCB.IsSymBackend sym bak )
                             => bak
                             -> LCLM.MemImpl sym
                             -> IO ( LCLM.MemImpl sym
                                   , LCSG.SymGlobalState sym) )

-- | Initial memory state for symbolic execution
data InitialMemory sym w =
  InitialMemory { imMemModel :: MemoryModel (LCS.GlobalVar (LCLM.LLVMPointerType w))
               -- ^ Which memory model configuration to use
                , imMemVar :: LCS.GlobalVar LCLM.Mem
               -- ^ MemVar to use in simulation
                , imGlobals :: LCSG.SymGlobalState sym
               -- ^ Initial global variables
                , imStackBasePtr :: LCLM.LLVMPtr sym w
               -- ^ Stack memory base pointer
                , imValidityCheck :: DMS.MkGlobalPointerValidityAssertion sym w
               -- ^ Additional pointer validity checks to enforce
                , imGlobalMap :: DMS.GlobalMap sym LCLM.Mem w
               -- ^ Globals used by the macaw translation; note that this is
               -- separate from the global variable map passed to crucible, as
               -- it is only used for initializing the macaw extension
                , imMemPtrTable :: AEM.MemPtrTable sym w
               -- ^ The global memory
                }

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
