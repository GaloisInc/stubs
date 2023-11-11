{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Stubs.Parser (parseStubsOverrides) where

import qualified Stubs.WeakAST as SWA
import qualified Stubs.ConcreteParser as SCP
import qualified Stubs.AST as SA
import qualified Stubs.Lower as SLow
import Control.Monad.Except (MonadIO(..))

-- | Top level function for reading and lowering stubs files.
parseStubsOverrides :: [FilePath] -> [String] -> SLow.StubsParserM SA.StubsProgram
parseStubsOverrides paths entryPoints = do
  weakModules <- liftIO $ mapM SCP.parseFile paths
  sigL <- mapM (\smod -> do
      SLow.genSigs (SWA.fns smod)
    ) weakModules
  let allSigs = concat sigL
  globL <- mapM (\smod -> do
      SLow.lowerGlobals (SWA.globals smod)
    ) weakModules
  let allGlobals = concat globL
  modIL <- mapM (\smod -> SLow.lowerModule smod allGlobals allSigs) weakModules
  let inits = concatMap snd modIL
  let mods = map fst modIL
  return SA.StubsProgram{SA.stubsModules=mods, SA.stubsEntryPoints=entryPoints, SA.stubsInitFns=inits}

