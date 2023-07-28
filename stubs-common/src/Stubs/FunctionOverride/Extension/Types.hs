{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Stubs.FunctionOverride.Extension.Types
  ( TypeAlias(..)
  , TypeLookup(..)
  , ExtensionParser
  , ExtensionWrapper(..)
  , SomeExtensionWrapper(..)
  , CrucibleSyntaxOverrides(..)
  , emptyCrucibleSyntaxOverrides
  , OverrideMapParseError(..)
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO )
import           Control.Monad.State.Class ( MonadState )
import           Control.Monad.Writer.Class ( MonadWriter )
import qualified Data.Aeson as DA
import qualified Data.Aeson.Key as DAK
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )

import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.Syntax.ExprParse as LCSE
import qualified Lang.Crucible.Types as LCT
import qualified What4.ProgramLoc as WP

import qualified Stubs.FunctionOverride as SF

-- | The additional types ambient-verifier supports beyond those built into
-- crucible-syntax.
data TypeAlias = Byte | Int | Long | PidT | Pointer | Short | SizeT | UidT
  deriving (Show, Eq, Enum, Bounded)

-- | Lookup function from a 'TypeAlias' to the underlying crucible type it
-- represents.
newtype TypeLookup = TypeLookup (TypeAlias -> (Some LCT.TypeRepr))

-- | The constraints on the abstract parser monad
type ExtensionParser m ext s = ( LCSE.MonadSyntax LCSA.Atomic m
                               , MonadWriter [WP.Posd (LCCR.Stmt ext s)] m
                               , MonadState (LCSC.SyntaxState s) m
                               , MonadIO m
                               , LCCE.IsSyntaxExtension ext
                               )

-- | A wrapper for a syntax extension statement
--
-- Note that these are pure and are intended to guide the substitution of syntax
-- extensions for operations in the 'MDS.MacawExt' syntax.
data ExtensionWrapper arch args ret =
  ExtensionWrapper { extName :: LCSA.AtomName
                  -- ^ Name of the syntax extension
                   , extArgTypes :: LCT.CtxRepr args
                  -- ^ Types of the arguments to the syntax extension
                   , extWrapper :: forall s m
                                 . ( ExtensionParser m (DMS.MacawExt arch) s)
                                => Ctx.Assignment (LCCR.Atom s) args
                                -> m (LCCR.AtomValue (DMS.MacawExt arch) s ret)
                  -- ^ Syntax extension wrapper that takes the arguments passed
                  -- to the extension operator, returning a suitable crucible
                  -- 'LCCR.AtomValue' to represent it in the syntax extension.
                   }

data SomeExtensionWrapper arch =
  forall args ret. SomeExtensionWrapper (ExtensionWrapper arch args ret)

-- | The overrides in a user-specified @--overrides@ directory that have gone
-- through a light round of validation checks.
data CrucibleSyntaxOverrides w p sym arch = CrucibleSyntaxOverrides
  { csoAddressOverrides :: Map.Map (SF.FunctionAddrLoc w)
                                   (NEL.NonEmpty (SF.SomeFunctionOverride p sym arch))
    -- ^ A map of @function address overrides@. These have been checked to
    --   ensure that every override that appears in the domain of the map
    --   corresponds to a @.cbl@ file.
  , csoStartupOverrides :: [SF.FunctionOverride p sym Ctx.EmptyCtx arch LCT.UnitType]
    -- ^ A list of @startup overrides@ in the order in which they should be
    --   executed at the start of simulation. These have been validated such
    --   that we know each override has no arguments and returns @Unit@.
  , csoNamedOverrides :: [SF.SomeFunctionOverride p sym arch]
    -- ^ An override for each @<name>.cbl@'s function of the corresponding
    --   @<name>@. These have been checked to ensure that the @.cbl@ file
    --   contents are valid and that there are no duplicate names.
  }

-- | An empty collection of 'CrucibleSyntaxOverrides'.
emptyCrucibleSyntaxOverrides :: CrucibleSyntaxOverrides w p sym ext
emptyCrucibleSyntaxOverrides = CrucibleSyntaxOverrides
  { csoAddressOverrides = Map.empty
  , csoStartupOverrides = []
  , csoNamedOverrides = []
  }

-- | Errors that can occur when parsing an @overrides.yaml@ file.
data OverrideMapParseError
  = ExpectedArray  DA.Value
  | ExpectedObject DA.Value
  | ExpectedString DA.Value
  | ExpectedAddress DAK.Key
  deriving (Show)

instance CMC.Exception OverrideMapParseError
