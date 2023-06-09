{-# LANGUAGE DeriveTraversable #-}

module Stubs.Loader.Versioning
  ( VersionedSymbol(..)
  , VersionedFunctionName
  , VersionedGlobalVarName
  ) where

import qualified Data.ByteString.Char8 as BSC
import qualified Prettyprinter as PP

import qualified Data.BinarySymbols as BinSym
import qualified What4.FunctionName as WF

-- | A symbol paired with version information.

-- This is very similar to VersionedSymbol in binary-symbols:Data.BinarySymbols,
-- except that this version is made more polymorphic to allow symbols besides
-- ByteStrings.
data VersionedSymbol sym = VerSym
  { versymSymbol :: !sym
  , versymVersion :: !BinSym.SymbolVersion
  } deriving (Eq, Foldable, Functor, Ord, Traversable, Show)

-- This code is cargo-culted from binary-symbols
-- (https://github.com/GaloisInc/flexdis86/blob/9b899ed652c80dd22aa7dd9f6920d0d13a077bf6/binary-symbols/src/Data/BinarySymbols.hs#L67-L76),
-- which is licensed under the 3-Clause BSD license.
instance PP.Pretty sym => PP.Pretty (VersionedSymbol sym) where
  pretty (VerSym sym ver) =
    PP.pretty sym PP.<>
      case ver of
        BinSym.UnversionedSymbol -> mempty
        BinSym.ObjectDefaultSymbol    v -> PP.pretty "@@" PP.<> PP.pretty (BSC.unpack v)
        BinSym.ObjectNonDefaultSymbol v -> PP.pretty  "@" PP.<> PP.pretty (BSC.unpack v)
        BinSym.VersionedSymbol soName symName
          -> PP.pretty '@' PP.<> PP.pretty (BSC.unpack symName) PP.<>
             PP.pretty '(' PP.<> PP.pretty (BSC.unpack soName)  PP.<> PP.pretty ')'

-- | A versioned 'WF.FunctionName'. This is a common enough instantiation of
-- 'VersionedSymbol' that we define a specific alias for it.
type VersionedFunctionName = VersionedSymbol WF.FunctionName

-- | A versioned 'BSC.ByteString' representing a global variable.
type VersionedGlobalVarName = VersionedSymbol BSC.ByteString
