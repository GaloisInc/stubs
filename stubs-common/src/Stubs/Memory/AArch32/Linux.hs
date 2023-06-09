{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeApplications #-}
module Stubs.Memory.AArch32.Linux (
    aarch32LinuxInitGlobals
  , aarch32LinuxStmtExtensionOverride
    -- * TLS
  , freshTLSGlobalVar
  ) where

import qualified Data.BitVector.Sized as BVS
import qualified Data.Text as DT

import qualified Data.Macaw.ARM as DMA
 -- Sometimes, GHC is unable to find instances of RegAddrWidth that are
 -- available by way of transitive module imports. The only reliable way of
 -- preventing this issue that I've found is to import the defining module for
 -- the instances directly. This is most likely a GHC bug (perhaps
 -- https://gitlab.haskell.org/ghc/ghc/-/issues/16234), but oh well.
import           Data.Macaw.ARM.ARMReg ()
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Common as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified What4.Interface as WI
import qualified What4.Symbol as WSym

import qualified Stubs.Memory as AM

-- | TLS pointer memory size in bytes
tlsMemorySize :: Integer
tlsMemorySize = 4 * 1024

-- | Create and initialize a pointer to store the TLS value.
-- See @Note [AArch32 and TLS]@ in "Ambient.FunctionOverride.AArch32.Linux".
initTLSMemory :: ( LCB.IsSymBackend sym bak
                 , LCLM.HasLLVMAnn sym
                 , ?memOpts :: LCLM.MemOptions
                 )
              => bak
              -> LCLM.MemImpl sym
                 -- ^ MemImpl to add the TLS pointer to
              -> IO ( LCLM.LLVMPtr sym (DMC.ArchAddrWidth DMA.ARM)
                      -- Base pointer for new TLS pointer
                    , LCLM.MemImpl sym
                      -- Updated MemImpl containing new TLS pointer
                    )
initTLSMemory bak mem0 = do
  let sym = LCB.backendGetSym bak
  let ?ptrWidth = WI.knownRepr
  arrayStorage <- WI.freshConstant sym (WSym.safeSymbol "tls") WI.knownRepr
  tlsMemorySizeBV <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr tlsMemorySize)
  oneByte <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr 1)
  (tlsPtr, mem1) <-
    LCLM.doCalloc bak mem0 tlsMemorySizeBV oneByte LCLD.noAlignment
  mem2 <- LCLM.doArrayStore bak
                            mem1
                            tlsPtr
                            LCLD.noAlignment
                            arrayStorage
                            tlsMemorySizeBV
  pure (tlsPtr, mem2)

-- | Allocate a fresh global variable representing TLS state.
freshTLSGlobalVar ::
  LCF.HandleAllocator ->
  IO (LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMA.ARM)))
freshTLSGlobalVar hdlAlloc =
  LCCC.freshGlobalVar hdlAlloc
                      (DT.pack "tls")
                      (LCLM.LLVMPointerRepr (WI.knownNat @32))

-- | This function takes a global variable for the TLS pointer
-- and returns an 'InitArchSpecificGlobals' that initializes the global
-- and inserts it into the global variable state.
aarch32LinuxInitGlobals ::
     ( ?memOpts :: LCLM.MemOptions
     )
  => LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMA.ARM))
     -- ^ Global variable for TLS
  -> AM.InitArchSpecificGlobals DMA.ARM
aarch32LinuxInitGlobals tlsGlob =
  AM.InitArchSpecificGlobals $ \bak mem0 -> do
    (tlsPtr, mem1) <- initTLSMemory bak mem0
    return (mem1, LCSG.insertGlobal tlsGlob tlsPtr LCSG.emptyGlobals)

-- | There are currently no overrides for macaw-aarch32-symbolic
aarch32LinuxStmtExtensionOverride :: DMS.MacawArchStmtExtensionOverride DMA.ARM
aarch32LinuxStmtExtensionOverride =
  DMS.MacawArchStmtExtensionOverride $ \_ _ -> return Nothing
