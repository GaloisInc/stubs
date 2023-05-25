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

module Stubs.Parser (parseCrucibleOverrides) where 

import qualified Control.Monad.Catch as CMC

import qualified Data.Aeson as DA
import qualified Data.Aeson.Key as DAK
import qualified Data.Aeson.KeyMap as DAKM
import qualified Data.ByteString as BS

import qualified Data.Parameterized.Nonce as Nonce

import qualified Data.Text as DT
import qualified Data.Text.IO as DTI
import qualified Data.Traversable as Trav
import qualified Data.Vector as DV
import qualified Data.Yaml as DY
import           Data.Word ( Word64 )

import qualified System.Directory as SD
import qualified System.FilePath as SF
import qualified System.FilePath.Glob as SFG
import qualified Text.Megaparsec as MP
import           Text.Read ( readMaybe )
import qualified Lang.Crucible.CFG.Extension as LCCE

import qualified Lang.Crucible.FunctionHandle as LCF

import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.Syntax.Concrete as LCSC

import qualified Lang.Crucible.Syntax.SExpr as LCSS

import qualified Stubs.Exception as SE

import           Stubs.FunctionOverride.Extension.Types
import qualified What4.FunctionName as WF

parseCrucibleOverrides :: LCCE.IsSyntaxExtension ext => FilePath
                            -> Nonce.NonceGenerator IO s
                            -> LCF.HandleAllocator
                            -> LCSC.ParserHooks ext
                            -> IO ([(FilePath,LCSC.ParsedProgram ext)],[ WF.FunctionName], [(FilePath, Word64,WF.FunctionName)])
parseCrucibleOverrides dir ng halloc hooks = do
  exists <- SD.doesDirectoryExist dir 
  if exists then do 
    let functionDir = dir SF.</> "function"
    cbls <- SFG.glob (functionDir SF.</> "*.cbl")
    ovmap <- traverse (\path -> (path,) <$> loadCblOverride path ng halloc hooks) cbls
    let overridesYamlPath = dir SF.</> "overrides.yaml"
    overridesYamlExists <- SD.doesFileExist overridesYamlPath
    mbOverridesYaml <- if overridesYamlExists then do 
                                                    bytes <- BS.readFile overridesYamlPath
                                                    val <- DY.decodeThrow bytes
                                                    pure $ Just val
                                              else pure Nothing
    funAddrOvs <- maybe (pure []) parseOverrideMap mbOverridesYaml
    startupOvs <- maybe (pure []) parseStartupOverrides mbOverridesYaml
    return (ovmap, startupOvs, funAddrOvs)
  else
    return ([],[],[])

-- | Parse the @function address overrides@ map in an @overrides.yaml@ file. If
-- no such map is present, return an empty list.
parseOverrideMap ::
  forall m.
  CMC.MonadThrow m =>
  DA.Value ->
  m [(FilePath, Word64, WF.FunctionName)]
parseOverrideMap val = do
  obj <- asObject val
  case DAKM.lookup "function address overrides" obj of
    Nothing -> pure []
    Just ovsVal -> do
      ovsObj <- asObject ovsVal
      ovs <- Trav.for (DAKM.toList ovsObj) $ \(bin, binVal) ->
               parseFunctionAddressOverrides (DAK.toString bin) binVal
      pure $ concat ovs
  where
    parseFunctionAddressOverrides ::
      FilePath -> DA.Value -> m [(FilePath, Word64, WF.FunctionName)]
    parseFunctionAddressOverrides bin binVal = do
      binObj <- asObject binVal
      traverse (\(addrKey, fun) -> do
                 addr <- case readMaybe (DAK.toString addrKey) of
                           Just addr -> pure addr
                           Nothing -> CMC.throwM $ ExpectedAddress addrKey
                 funName <- asString fun
                 pure (bin, addr, WF.functionNameFromText funName))
               (DAKM.toList binObj)

-- | Parse the @startup overrides@ list in an @overrides.yaml@ file. If no such
-- list is present, return an empty list.
parseStartupOverrides ::
  CMC.MonadThrow m =>
  DA.Value ->
  m [WF.FunctionName]
parseStartupOverrides val = do
  obj <- asObject val
  case DAKM.lookup "startup overrides" obj of
    Nothing -> pure []
    Just ovsVal -> do
      ovsArr <- asArray ovsVal
      ovsArr' <- traverse (\fun -> do
                            funName <- asString fun
                            pure $ WF.functionNameFromText funName)
                          ovsArr
      pure $ DV.toList ovsArr'

-- | Assert that a JSON 'DA.Value' is an 'DA.Array'. If this is the case,
-- return the underlying array. Otherwise, throw an exception.
asArray :: CMC.MonadThrow m => DA.Value -> m DA.Array
asArray (DA.Array a) = pure a
asArray val          = CMC.throwM $ ExpectedArray val

-- | Assert that a JSON 'DA.Value' is a 'DA.String'. If this is the case,
-- return the underlying text. Otherwise, throw an exception.
asString :: CMC.MonadThrow m => DA.Value -> m DT.Text
asString (DA.String t) = pure t
asString val           = CMC.throwM $ ExpectedString val

-- | Assert that a JSON 'DA.Value' is an 'DA.Object'. If this is the case,
-- return the underlying object. Otherwise, throw an exception.
asObject :: CMC.MonadThrow m => DA.Value -> m DA.Object
asObject (DA.Object o) = pure o
asObject val           = CMC.throwM $ ExpectedObject val

-- | Read and parse a single @.cbl@ override file.
loadCblOverride
  :: LCCE.IsSyntaxExtension ext
  => FilePath
  -- ^ Path to @.cbl@ file to load
  -> Nonce.NonceGenerator IO s
  -> LCF.HandleAllocator
  -> LCSC.ParserHooks ext
  -- ^ ParserHooks for the desired syntax extension
  -> IO (LCSC.ParsedProgram ext)
loadCblOverride path ng halloc hooks = do
  contents <- DTI.readFile path
  parseCrucibleSyntaxOverride path contents SE.CblOverride ng halloc hooks

-- | Parse a single crucible syntax override.
parseCrucibleSyntaxOverride
  :: LCCE.IsSyntaxExtension ext
  => FilePath
  -- ^ The file containing the syntax override. This is only used for
  -- error message purposes.
  -> DT.Text
  -- ^ The textual contents of a syntax override
  -> SE.OverrideLang
  -- ^ The language that the original override was written in. This is used
  -- to make the error messages more descriptive if the original override was
  -- written in C.
  -> Nonce.NonceGenerator IO s
  -> LCF.HandleAllocator
  -> LCSC.ParserHooks ext
  -- ^ ParserHooks for the desired syntax extension
  -> IO (LCSC.ParsedProgram ext)
parseCrucibleSyntaxOverride path contents ovLang ng halloc hooks = do
  let parsed = MP.parse (  LCSS.skipWhitespace
                        *> MP.many (LCSS.sexp LCSA.atom)
                        <* MP.eof)
                        path
                        contents
  case parsed of
    Left err -> CMC.throwM (SE.CrucibleSyntaxMegaparsecFailure ovLang contents err)
    Right asts -> do
      let ?parserHooks = hooks
      eAcfgs <- LCSC.top ng halloc [] $ LCSC.prog asts
      case eAcfgs of
        Left err -> CMC.throwM (SE.CrucibleSyntaxExprParseFailure ovLang contents err)
        Right parsedProg -> pure parsedProg