{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Stubs.EnvVar
  ( ConcreteEnvVar(..)
  , ConcreteEnvVarFromBytes(..)
  , SymbolicEnvVar(..)
  , EnvVarParser
  , concreteEnvVarParser
  , concreteEnvVarFromBytesParser
  , symbolicEnvVarParser
  , mkEnvVarMap
  ) where

import qualified Control.Applicative as App
import qualified Control.Applicative.Combinators as CAC
import qualified Data.Aeson as DA
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import qualified Data.String as Str
import qualified Data.Text as DT
import qualified Data.Traversable as T
import           Data.Void ( Void )
import qualified Text.Megaparsec as TM
import qualified Text.Megaparsec.Char as TMC

import qualified Lang.Crucible.Backend as LCB
import qualified What4.Interface as WI

-- | An environment variable definition consisting of a key-value pair of
-- strings, both of which are concrete.
data ConcreteEnvVar s = ConcreteEnvVar s s
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

instance (s ~ DT.Text) => DA.FromJSON (ConcreteEnvVar s) where
  parseJSON = DA.withText "ConcreteEnvVar" $ \t ->
    case TM.parse concreteEnvVarParser "" t of
      Left err -> fail $ "Could not parse concrete environment variable: "
                      ++ TM.errorBundlePretty err
      Right r  -> pure r

-- | An environment variable definition consisting of a key and a file
-- containing the value corresponding to the key.
data ConcreteEnvVarFromBytes s = ConcreteEnvVarFromBytes s FilePath
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

instance (s ~ DT.Text) => DA.FromJSON (ConcreteEnvVarFromBytes s) where
  parseJSON = DA.withText "ConcreteEnvVarFromBytes" $ \t ->
    case TM.parse concreteEnvVarFromBytesParser "" t of
      Left err -> fail $ "Could not parse concrete environment variable from bytes: "
                      ++ TM.errorBundlePretty err
      Right r  -> pure r

-- | An environment variable definition where the key is concrete, but the
-- value is symbolic. Only the length of the value (represented as an 'Int')
-- is known. Note that the length does not incude the null terminator at the
-- end.
data SymbolicEnvVar s = SymbolicEnvVar s Int
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

instance (s ~ DT.Text) => DA.FromJSON (SymbolicEnvVar s) where
  parseJSON = DA.withText "SymbolicEnvVar" $ \t ->
    case TM.parse symbolicEnvVarParser "" t of
      Left err -> fail $ "Could not parse symbolic environment variable: "
                      ++ TM.errorBundlePretty err
      Right r  -> pure r

-- | A @megaparsec@ parser type for environment variables.
type EnvVarParser s = TM.Parsec Void s

-- | A @megaparsec@ parser for 'ConcreteEnvVar's.
concreteEnvVarParser ::
     forall s.
     ( Str.IsString s
     , TM.VisualStream s
     , TM.TraversableStream s
     , TM.Token s ~ Char
     , TM.Tokens s ~ s
     )
  => EnvVarParser s (ConcreteEnvVar s)
concreteEnvVarParser = do
  key <- TM.takeWhileP (Just "key") (/= '=')
  _ <- TMC.char '='
  val <- TM.takeRest
  pure $ ConcreteEnvVar key val

-- | A @megaparsec@ parser for 'ConcreteEnvVarFromBytes'.
concreteEnvVarFromBytesParser ::
  EnvVarParser DT.Text (ConcreteEnvVarFromBytes DT.Text)
concreteEnvVarFromBytesParser = do
  key <- TM.takeWhileP (Just "key") (/= '[')
  file <- CAC.between (TMC.char '[') (TMC.char ']') $
          TM.takeWhileP (Just "file") (/= ']')
  pure $ ConcreteEnvVarFromBytes key (DT.unpack file)

-- | A @megaparsec@ parser for 'SymbolicEnvVar's.
symbolicEnvVarParser ::
     forall s.
     ( Str.IsString s
     , TM.VisualStream s
     , TM.TraversableStream s
     , TM.Token s ~ Char
     , TM.Tokens s ~ s
     )
  => EnvVarParser s (SymbolicEnvVar s)
symbolicEnvVarParser = do
  key <- TM.takeWhileP (Just "key") (/= '[')
  lenStr <- CAC.between (TMC.char '[') (TMC.char ']') (App.many TMC.digitChar)
  pure $ SymbolicEnvVar key (read lenStr)

-- | Read the bytes of a 'ConcreteEnvVarFromBytes' file and convert it to a
-- 'ConcreteEnvVar'.
readConcreteEnvVarFromBytes ::
     ConcreteEnvVarFromBytes BS.ByteString
  -> IO (ConcreteEnvVar BS.ByteString)
readConcreteEnvVarFromBytes (ConcreteEnvVarFromBytes key file) = do
  val <- BS.readFile file
  pure $ ConcreteEnvVar key val

-- | Construct a 'Map.Map' from each environment variable's key to its value.
-- This will convert all of the bytes in each value to 'WI.SymBV's in the
-- process.
--
-- Note that this does /not/ preserve the order in which the user supplied the
-- environment variables (on the command line or otherwise). If there are any
-- exploits that rely on the particular order of elements in the
-- @envp@/@environ@ array, we will need to revisit this choice.
mkEnvVarMap ::
     LCB.IsSymBackend sym bak
  => bak
  -> [ConcreteEnvVar BS.ByteString]
  -> [ConcreteEnvVarFromBytes BS.ByteString]
  -> [SymbolicEnvVar BS.ByteString]
  -> IO (Map.Map BS.ByteString [WI.SymBV sym 8])
mkEnvVarMap bak cevs cevfbs sevs = do
  let sym = LCB.backendGetSym bak
  let w8 = WI.knownNat @8
  let map0 = Map.empty

  cevfbs' <- traverse readConcreteEnvVarFromBytes cevfbs
  let allCevs = cevs ++ cevfbs'

  -- First, add all of the concrete environment variables...
  map1 <-
    F.foldlM
      (\m (ConcreteEnvVar key val) ->
        do val' <- T.for (BS.unpack val) $ \byte ->
                   WI.bvLit sym w8 $ BVS.mkBV w8
                                   $ fromIntegral byte
           pure $ Map.insert key val' m)
      map0
      allCevs

  -- ...then, add all of the symbolic environment variables.
  F.foldlM
    (\m (SymbolicEnvVar key valLen) ->
      do loc <- WI.getCurrentProgramLoc sym
         val <- ireplicateM valLen $ \i ->
                do let name = BSC.unpack key ++ "_envVar_" ++ show i
                   valByte <-
                     WI.freshConstant sym (WI.safeSymbol name) (WI.BaseBVRepr w8)

                   -- Only the end of the C string is allowed to be the null
                   -- terminator.
                   valNonNull <- WI.bvIsNonzero sym valByte
                   let desc = name ++ " non-null"
                   LCB.addAssumption bak $
                     LCB.GenericAssumption loc desc valNonNull

                   pure valByte
         pure $ Map.insert key val m)
    map1
    sevs

ireplicateM :: forall f a. Applicative f => Int -> (Int -> f a) -> f [a]
ireplicateM n f = go 0
  where
    go :: Int -> f [a]
    go !i | i >= n    = pure []
          | otherwise = (:) <$> f i <*> go (i + 1)
