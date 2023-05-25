{-# LANGUAGE GADTs #-}
module Stubs.Loader.ELF.DecodeError
  ( throwDecodeFailure
  ) where

import qualified Control.Monad.Catch as CMC
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import           Data.Parameterized.Some ( Some(..) )

import qualified PE.Parser as PE

import qualified Stubs.Exception as AE

-- | We failed to decode an ELF binary, so give as descriptive of an error
-- message as possible.
throwDecodeFailure ::
  CMC.MonadThrow m =>
  FilePath ->
  -- ^ The path to the ELF binary
  BS.ByteString ->
  -- ^ The contents of the ELF binary
  m a
throwDecodeFailure elfName elfBytes =
  case PE.decodePEHeaderInfo (BSL.fromStrict elfBytes) of
    Right (Some _) -> CMC.throwM (AE.UnsupportedPEArchitecture elfName)
    Left _ -> CMC.throwM (AE.UnsupportedBinaryFormat elfName)
