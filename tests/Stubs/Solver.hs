{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
-- | This module provides an interface for instantiating SMT solvers
--
-- The intent of this module is to make it easy to select a solver from the
-- command line (i.e., via a flag), while still introducing all of the complex
-- existentials necessary for introducing solver state types and typeclass
-- constraints.
module Stubs.Solver (
    Solver(..)
  , FloatMode(..)
  , withOnlineSolver
  , offlineSolver
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(..) )
import qualified Data.Parameterized.Nonce as PN
import qualified What4.Expr as WE
import qualified What4.ProblemFeatures as WP
import qualified What4.Protocol.Online as WPO
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO

import qualified Stubs.Exception as AE

-- | The solver to use
--
-- This can be the solver used for online path satisfiability checking or for
-- discharging individual verification conditions
data Solver = Boolector
            | CVC4
            | CVC5
            | Yices
            | Z3
            deriving (Read, Show, Eq, Ord)

-- | The interpretation of floating point operations
data FloatMode = IEEE
               -- ^ Use a bit-precise interpretation; this is the most faithful
               -- to the program semantics, but often yields queries that are unsolvable
               | Real
               -- ^ Approximate floating point operations as reals; this is
               -- scalable, but not entirely faithful to the machine
               -- semantics. In particular, it doesn't provide any way to reason
               -- about precision, NaN, or denormal values.
               | UF
               -- ^ Leave floating point operations uninterpreted
               --
               -- This can yield false positive models, and is usually only
               -- suitable for syntactic equivalence queries
               deriving (Read, Show, Eq, Ord)

-- | Get the offline adapter for the requested solver
offlineSolver :: Solver -> WS.SolverAdapter st
offlineSolver s =
  case s of
    Boolector -> WS.boolectorAdapter
    CVC4 -> WS.cvc4Adapter
    CVC5 -> WS.cvc5Adapter
    Yices -> WS.yicesAdapter
    Z3 -> WS.z3Adapter

-- | Run a continuation with the selected solver and floating point interpretation
--
-- This function provides an online solver suitable for path satisfiability
-- checking.
withOnlineSolver
  :: forall m scope a
   . (MonadIO m, CMC.MonadMask m)
  => Solver
  -> FloatMode
  -> PN.NonceGenerator IO scope
  -> ( forall sym bak solver st fs
      . ( sym ~ WE.ExprBuilder scope st fs
        , bak ~ LCBO.OnlineBackend solver scope st fs
        , LCB.IsSymBackend sym bak
        , WPO.OnlineSolver solver
        )
     => bak -> m a
     )
  -> m a
withOnlineSolver solver fm ng k =
  case solver of
    Boolector ->
      -- See Note [Float Mode Duplication]
      case fm of
        IEEE -> CMC.throwM (AE.UnsupportedSolverCombination (show solver) (show fm))
        Real -> CMC.throwM (AE.UnsupportedSolverCombination (show solver) (show fm))
        UF   -> withSym WE.FloatUninterpretedRepr $ \sym ->
                LCBO.withBoolectorOnlineBackend sym LCBO.NoUnsatFeatures k
    CVC4 ->
      case fm of
        IEEE -> withSym WE.FloatIEEERepr $ \sym ->
                LCBO.withCVC4OnlineBackend sym LCBO.NoUnsatFeatures WP.noFeatures k
        Real -> withSym WE.FloatRealRepr $ \sym ->
                LCBO.withCVC4OnlineBackend sym LCBO.NoUnsatFeatures WP.noFeatures k
        UF   -> withSym WE.FloatUninterpretedRepr $ \sym ->
                LCBO.withCVC4OnlineBackend sym LCBO.NoUnsatFeatures WP.noFeatures k
    CVC5 ->
      case fm of
        IEEE -> withSym WE.FloatIEEERepr $ \sym ->
                LCBO.withCVC5OnlineBackend sym LCBO.NoUnsatFeatures WP.noFeatures k
        Real -> withSym WE.FloatRealRepr $ \sym ->
                LCBO.withCVC5OnlineBackend sym LCBO.NoUnsatFeatures WP.noFeatures k
        UF   -> withSym WE.FloatUninterpretedRepr $ \sym ->
                LCBO.withCVC5OnlineBackend sym LCBO.NoUnsatFeatures WP.noFeatures k
    Yices ->
      case fm of
        IEEE -> CMC.throwM (AE.UnsupportedSolverCombination (show solver) (show fm))
        -- Without 'useSymbolicArrays' what4 attempts to generate terms that
        -- Yices doesn't support and throws an exception
        Real -> withSym WE.FloatRealRepr $ \sym ->
                LCBO.withYicesOnlineBackend sym LCBO.NoUnsatFeatures WP.useSymbolicArrays k
        UF   -> withSym WE.FloatUninterpretedRepr $ \sym ->
                LCBO.withYicesOnlineBackend sym LCBO.NoUnsatFeatures WP.useSymbolicArrays k
    Z3 ->
      case fm of
        IEEE -> withSym WE.FloatIEEERepr $ \sym ->
                LCBO.withZ3OnlineBackend sym LCBO.NoUnsatFeatures WP.noFeatures k
        Real -> withSym WE.FloatRealRepr $ \sym ->
                LCBO.withZ3OnlineBackend sym LCBO.NoUnsatFeatures WP.noFeatures k
        UF   -> withSym WE.FloatUninterpretedRepr $ \sym ->
                LCBO.withZ3OnlineBackend sym LCBO.NoUnsatFeatures WP.noFeatures k
  where
    withSym :: WE.FloatModeRepr fm
            -> (forall st. WE.ExprBuilder scope st (WE.Flags fm) -> m a)
            -> m a
    withSym fmr symAction = do
      sym <- liftIO $ WE.newExprBuilder fmr WE.EmptyExprBuilderState ng
      symAction sym

{- Note [Float Mode Duplication]

The duplication here is unfortunate, but we have to do it because there is no
good way to capture the floating point interface constraint without a literal
repr here. There doesn't seem to be a better way to do this because we need the
repr to instantiate the symbolic interface, but we can't get the appropriate
instance without having a symbolic interface. This duplication (and therefore
inlining of the reprs) breaks the cyclic dependency.

-}
