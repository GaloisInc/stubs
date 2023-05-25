module Stubs.Loader.Relocations
  ( RelocType(..)
  ) where

-- | An architecture-independent description of the type of a relocation. When
-- appropriate, this groups together certain relocation types that have
-- identical treatment in the verifier.
data RelocType
  = CopyReloc
    -- ^ A @COPY@ relocation (e.g., @R_ARM_COPY@). These reference the value of
    -- a global variable in a separate shared library.
  | SymbolReloc
    -- ^ A relocation that references the address of a symbol, plus an offset.
    -- These include absolute references to symbols in the same shared library
    -- (e.g., @R_ARM_ABS32@) and global variables defined in separate shared
    -- libraries (e.g., @R_ARM_GLOB_DAT@).
  | RelativeReloc
    -- ^ A @RELATIVE@ relocation (e.g., @R_ARM_RELATIVE@). These reference an
    -- address relative to the load address of a shared library.
