{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Stubs.Loader.ELF.DynamicLoader
  ( loadDynamicDependencies
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(..) )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Type.Equality as DTE
import qualified System.Directory as SD
import qualified System.FilePath as SF

import qualified Data.ElfEdit as DE
import qualified Data.Macaw.BinaryLoader as DMB

import qualified Stubs.Exception as AE
import qualified Stubs.Loader.ELF.DecodeError as ALEDE
import qualified Stubs.Loader.LoadOptions as ALL

-- | Given a binary, load all of the shared libraries that it transitively
-- depends on, returning the order in which they were encountered in a
-- breadth-first search. Returning them in this order is important since we
-- rely on the assumption that the binaries are in the same order as the global
-- lookup scope. See @Note Note [Dynamic lookup scope]@.
loadDynamicDependencies ::
  forall m arch binFmt w.
  ( MonadIO m
  , CMC.MonadThrow m
  , DMB.BinaryLoader arch binFmt
  , binFmt ~ DE.ElfHeaderInfo w
  ) =>
  DE.ElfMachine ->
  -- ^ The architecture of the main binary (x86_64, AArch32, etc.)
  DE.ElfClass w ->
  -- ^ Whether the main binary is 32-bit or 64-bit
  FilePath ->
  -- ^ The directory in which the shared libraries live
  DMB.LoadedBinary arch binFmt ->
  -- ^ The main binary
  FilePath ->
  -- ^ The main binary's path
  m [(DMB.LoadedBinary arch binFmt, FilePath)]
  -- ^ The shared libraries in order of global lookup scope, paired with their
  -- file paths
loadDynamicDependencies expectedHeaderMachine expectedHeaderClass sharedObjectDir mainBinary mainBinaryPath =
   -- First, parse the DT_NEEDED entries of the main binary.
   case parseDynNeeded (DMB.originalBinary mainBinary) mainBinaryPath of
     -- If this returns Nothing, the binary isn't dynamically linked.
     -- We return an empty list of shared libraries in this case.
     Nothing -> pure []
     -- Otherwise, proceed with a breadth-first search of the DT_NEEDED entries
     -- in each of the shared libraries.
     Just dynNeededs -> do
       dynNeededs' <- either CMC.throwM pure dynNeededs
       go Set.empty 1 $ Seq.fromList dynNeededs'
  where
    -- The main loop in the breadth-first search.
    go ::
      Set.Set BS.ByteString ->
      -- ^ The set of shared libraries that we have already loaded.
      Int ->
      -- ^ The index of the next shared library to load. This will be used to
      --   determine the address offsets for that shared library. See
      --   @Note [Address offsets for shared libraries]@ in
      --   "Ambient.Loader.LoadOptions".
      Seq.Seq (BS.ByteString) ->
      -- ^ The queue of @DT_NEEDED@ entries that need to be processed.
      m [(DMB.LoadedBinary arch binFmt, FilePath)]
    go sosSeenSoFar !nextSoIdx dynQueue =
      case Seq.viewl dynQueue of
        Seq.EmptyL -> pure []
        dynNext Seq.:< dynRest
          |  -- If we have already loaded this shared library, skip it and
             -- process the rest of the queue
             dynNext `Set.member` sosSeenSoFar
          -> go sosSeenSoFar nextSoIdx dynRest
          |  otherwise
          -> do let dynNextFP = BSC.unpack dynNext
                let fullPath = sharedObjectDir SF.</> dynNextFP
                exists <- liftIO $ SD.doesFileExist fullPath
                -- We only attempt to load a shared library if it exists on the
                -- user-specified path. Otherwise, we skip it and process the
                -- rest of the queue. This choice is a bit strange, but it's
                -- common for --shared-objects to omit things like libc.so
                -- because there are overrides for each of the libc functions
                -- being invoked. We don't want to crash in these situations,
                -- so we have to be a bit lenient.
                if exists
                  then do -- Read the shared library from disk and load it.
                          soBytes <- liftIO $ BS.readFile fullPath
                          so <- loadSharedObject nextSoIdx dynNextFP soBytes
                          case parseDynNeeded (DMB.originalBinary so) dynNextFP of
                            -- By definition, each of the shared libraries
                            -- should be dynamically linked. If they're not,
                            -- something very fishy is going on, so throw an
                            -- error.
                            Nothing -> CMC.throwM $ AE.ElfNonDynamicSharedLib dynNextFP
                            -- Otherwise, return the loaded shared library and
                            -- proceed. In the process of doing so, we add the
                            -- shared library to the set of already loaded
                            -- libraries, increment the index, and add the
                            -- DT_NEEDED entries from the shared library to the
                            -- back of the queue.
                            Just dynNeededs -> do
                              dynNeededs' <- either CMC.throwM pure dynNeededs
                              sos <- go (Set.insert dynNext sosSeenSoFar)
                                        (nextSoIdx + 1)
                                        (dynRest <> Seq.fromList dynNeededs')
                              pure ((so, dynNextFP):sos)
                   else go sosSeenSoFar nextSoIdx dynRest

    -- Load a shared library from disk.
    loadSharedObject ::
      Int ->
      -- ^ The index of the next shared library to load. This will be used to
      --   determine the address offsets for that shared library. See
      --   @Note [Address offsets for shared libraries]@ in
      --   "Ambient.Loader.LoadOptions".
      FilePath ->
      -- ^ The path to the shared library
      BS.ByteString ->
      -- ^ The contents of the shared library
      m (DMB.LoadedBinary arch binFmt)
    loadSharedObject index soName soBytes =
      case DE.decodeElfHeaderInfo soBytes of
        Right (DE.SomeElf ehi) -> do
          let hdr = DE.header ehi
          if DE.headerMachine hdr == expectedHeaderMachine
          then
            case DTE.testEquality (DE.headerClass hdr) expectedHeaderClass of
              Just DTE.Refl -> do
                let options = ALL.indexToLoadOptions (fromIntegral index)
                DMB.loadBinary options ehi
              _ -> CMC.throwM (AE.SoMismatchedElfClass (DE.headerClass hdr)
                                                       expectedHeaderClass)
          else CMC.throwM (AE.SoMismatchedElfMachine (DE.headerMachine hdr)
                                                     expectedHeaderMachine)
        Left _ -> ALEDE.throwDecodeFailure soName soBytes

-- | Get values of @DT_NEEDED@ entries in an ELF file. If this is not a dynamic
-- executable, then @Nothing@ is returned.
--
-- This is adapted from code in reopt
-- (https://github.com/GaloisInc/reopt/blob/81e8cce7482bd0caa78e086296cab1add430e394/src/Reopt.hs#L1517-L1539),
-- licensed under the 3-Clause BSD license.
parseDynNeeded ::
  DE.ElfHeaderInfo w ->
  FilePath ->
  -- ^ The path to the ELF file
  Maybe (Either AE.AmbientException [BS.ByteString])
parseDynNeeded elfHeaderInfo elfFP = DE.elfClassInstances elfClass $
  case filter (\p -> DE.phdrSegmentType p == DE.PT_DYNAMIC) elfPhdrs of
    [dynPhdr] -> Just $
      let dynContents = DE.slice (DE.phdrFileRange dynPhdr) elfBytes
      in case DE.dynamicEntries (DE.headerData elfHeader) elfClass dynContents of
           Left dynError ->
             Left $ AE.ElfDynamicParseError elfFP dynError
           Right dynSection -> do
             case DE.virtAddrMap elfBytes elfPhdrs of
               Nothing -> do
                 Left $ AE.ElfVirtualAddressMapError elfFP
               Just phdrs ->
                 case DE.dynNeeded dynSection phdrs of
                   Left errMsg -> Left $ AE.ElfDynamicNeededError elfFP errMsg
                   Right deps -> Right deps
    [] -> Nothing
    _  -> Just $ Left $ AE.ElfMultipleDynamicHeaders elfFP
  where
    elfHeader = DE.header elfHeaderInfo
    elfPhdrs = DE.headerPhdrs elfHeaderInfo
    elfBytes = DE.headerFileContents elfHeaderInfo
    elfClass = DE.headerClass elfHeader

{-
Note [Dynamic lookup scope]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
When looking up a dynamically linked function, which shared libraries should be
searched, and in which order? Answering this question precisely is tricky.

Section 1.5.4 of "How to Write Shared Libraries" on lookup scopes
(https://www.cs.dartmouth.edu/~sergey/cs258/ABI/UlrichDrepper-How-To-Write-Shared-Libraries.pdf)
offers a very detailed answer, although it is quite involved since it tries
to specify the behavior of `dlopen`. The verifier needs to care about lookup
scopes to some degree, since it affects the semantics of dynamically linked
programs, but for now we prefer to pretend that `dlopen` isn't a thing. To
borrow section 1.5.4's jargon, that means that we need to simulate the _global_
lookup scope, but not local lookup scopes.

When the verifier loads shared libraries, it returns them in the order dictated
by the global scope. An ELF binary's direct shared library dependencies are
contained in the DT_NEEDED entries, so to determine the global scope, we
perform a breadth-first search over the DT_NEEDED entries of the main binary
and the entries of the libraries that it depends on. See
`loadDynamicDependencies` for the full details.

Having the loaded binaries be in the same order as the global scope becomes
important when resolving dynamic function symbols. It's possible for two
binaries to define different functions of the same name. For example, imagine
this scenario:

  // a.c
  char f() { return 'a'; }

  // b.c
  char f() { return 'b'; }

  // main.c
  char f();
  int main() { printf("%c\n", f()); }

Suppose a.c and b.c are compiled to shared libraries liba.so and libb.so,
respectively, and that main.c is compiled to a main.exe binary that links
against both liba and libb. What will main.exe print when invoked? The
answer depends on the order of DT_NEEDED entries in main.exe, which in turn
depends on the order in which main.exe was linked against liba and libb when
compiled. If it was compiled like so:

  gcc -L. -la -lb main.c -o main.exe

Then the global scope will be:

  [main.exe, liba.so, libb.so]

And looking up f() will find libba first, causing 'a' to be printed. By a
similar token, if main.exe is compiled with `-lb -la` instead, then main.exe
would print 'b'.

This search order is implemented in the verifier in
A.Loader.ELF.Symbols.elfDynamicSymbolMap, which puts all of the dynamic symbols
in a binary into a single Map. The symbols will be inserted into the map in the
order the binaries appear in the global scope, and in the event that we
encounter a symbol that has already been inserted into the map, we will always
prefer the already-inserted symbol, as that appears first in the global scope.

It's worth emphasizing that this implementation fundamentally relies on the
absence of dlopen. If we need to model dlopen in the future, we will have to
pick a more sophisticated implementation approach.
-}
