{-| Define supported ABIs -}
module Stubs.ABI (
    ABI(..)
  , allABIs
  ) where

-- | ABIs supported by the verifier
data ABI = X86_64Linux | AArch32Linux
  deriving (Read, Show, Eq, Enum, Bounded)

-- | A list of all supported ABIs
allABIs :: [ABI]
allABIs = [minBound .. maxBound]

