{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | Functionality for resolving symbolic expressions as concrete.
--
-- Much of this code is copied from PATE (https://github.com/GaloisInc/pate),
-- which is licensed under the 3-Clause BSD license.
module Stubs.Verifier.Concretize
  ( Concretize
  , concreteBV
  , concreteInteger
  , resolveSingletonSymbolic
  , resolveSingletonSymbolicAs
  , ResolutionFailure(..)
  , resolveSingletonPointer
  , ResolveSymBVEffect(..)
  , resolveSymBV
  , resolveSymBVAs
  , resolveSymNat
  ) where

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Traversable as T
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified What4.BaseTypes as WT
import qualified What4.Expr as WE
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat
import qualified What4.Utils.BVDomain as WUB
import qualified What4.Utils.BVDomain.Arith as WUBA
import qualified What4.Utils.ResolveBounds.BV as WURB

import qualified Stubs.Panic as AP

data Concretize sym tp where
  Concretize :: (Show (WEG.GroundValue tp))
             => WT.BaseTypeRepr tp
             -> (WI.SymExpr sym tp -> Maybe (WEG.GroundValue tp)) -- Convert a symbolic term to a concrete value
             -> (sym -> WI.SymExpr sym tp -> WEG.GroundValue tp -> IO (WI.SymExpr sym WT.BaseBoolType)) -- Create a blocking clause from a concrete value
             -> (sym -> WEG.GroundValue tp -> IO (WI.SymExpr sym tp)) -- Create a symbolic term wrapping the concrete result
             -> Concretize sym tp

concreteBV :: (LCB.IsSymInterface sym, 1 <= w) => PN.NatRepr w -> Concretize sym (WI.BaseBVType w)
concreteBV w = Concretize (WT.BaseBVRepr w) WI.asBV toBlocking injectSymbolic
  where
    toBlocking sym symVal gv = WI.notPred sym =<< WI.bvEq sym symVal =<< WI.bvLit sym w gv
    injectSymbolic sym gv = WI.bvLit sym w gv

concreteInteger :: (LCB.IsSymInterface sym) => Concretize sym WI.BaseIntegerType
concreteInteger = Concretize WT.BaseIntegerRepr WI.asInteger toBlocking injectSymbolic
  where
    toBlocking sym symVal gv = WI.notPred sym =<< WI.intEq sym symVal =<< WI.intLit sym gv
    injectSymbolic = WI.intLit

-- | Reasons why attempting to resolve a symbolic expression as concrete can
-- fail.
data ResolutionFailure
  = SolverUnknown
    -- ^ Querying the SMT solver yielded @UNKNOWN@.
  | UnsatInitialAssumptions
    -- ^ Querying the SMT solver for an initial model of the expression failed
    --   due to the initial assumptions in scope being unsatisfiable.
  | MultipleModels
    -- ^ There are multiple possible models for the expression, which means it
    --   is truly symbolic and therefore unable to be concretized.
  deriving Show

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using the SMT solver
--
-- This asks for a model. If it gets one, it adds a blocking clause and asks for
-- another. If there was only one model, concretize the initial value and return
-- it with 'Right'. Otherwise, return an explanation of why concretization
-- failed with 'Left'.
resolveSingletonSymbolicAs
  :: ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , HasCallStack
     )
  => Concretize sym tp
  -- ^ The strategy for concretizing the type
  -> LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> WI.SymExpr sym tp
  -- ^ The symbolic term to concretize
  -> IO (Either ResolutionFailure (WEG.GroundValue tp))
resolveSingletonSymbolicAs (Concretize _tp asConcrete toBlocking _injectSymbolic) bak val =
  let sym = LCB.backendGetSym bak in
  case asConcrete val of
    Just val' -> return $ Right val'
    Nothing -> do
      LCBO.withSolverProcess bak (onlinePanic "resolveSingletonSymbolicValue") $ \sp -> do
        res <- WPO.inNewFrame sp $ do
          msat <- WPO.checkAndGetModel sp "Concretize value (with no assumptions)"
          mmodel <- case msat of
            WSat.Unknown -> return $ Left SolverUnknown
            WSat.Unsat {} -> return $ Left UnsatInitialAssumptions
            WSat.Sat mdl -> return $ Right mdl
          T.forM mmodel $ \mdl -> WEG.groundEval mdl val
        case res of
          Left _failure -> return res -- We failed to get a model
          Right concVal -> do
            WPO.inNewFrame sp $ do
              block <- toBlocking sym val concVal
              WPS.assume (WPO.solverConn sp) block
              msat <- WPO.checkAndGetModel sp "Concretize value (with blocking clause)"
              case msat of
                WSat.Unknown -> return $ Left SolverUnknown -- Total failure
                WSat.Sat _mdl -> return $ Left MultipleModels  -- There are multiple models
                WSat.Unsat {} -> return res -- There is a single concrete result

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using the SMT solver
--
-- This asks for a model. If it gets one, it adds a blocking clause and asks for
-- another. If there was only one model, concretize the initial value and return
-- it. Otherwise, return the original symbolic value.
resolveSingletonSymbolic ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , HasCallStack
     )
  => Concretize sym tp
  -- ^ The strategy for concretizing the type
  -> LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> WI.SymExpr sym tp
  -- ^ The symbolic term to concretize
  -> IO (WI.SymExpr sym tp)
resolveSingletonSymbolic concretize@(Concretize _ _ _ injectSymbolic) bak val = do
  let sym = LCB.backendGetSym bak
  res <- resolveSingletonSymbolicAs concretize bak val
  case res of
    Left _        -> pure val
    Right concVal -> injectSymbolic sym concVal

onlinePanic :: String -> a
onlinePanic fnName = AP.panic AP.Verifier fnName ["Online solver support is not enabled"]

-- | Resolve a 'WI.SymNat' to concrete, if possible.
resolveSymNat ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , HasCallStack
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> WI.SymNat sym
  -- ^ The symbolic natural number to concretize
  -> IO (WI.SymNat sym)
resolveSymNat bak symNat = do
  let sym = LCB.backendGetSym bak
  symInt <- WI.natToInteger sym symNat
  resolvedSymInt <- resolveSingletonSymbolic concreteInteger bak symInt
  WI.integerToNat sym resolvedSymInt

-- | The effect that 'resolveSymBV' had on the passed-in bitvector
data ResolveSymBVEffect = Concretized | RefinedBounds | UnchangedBounds

-- | Resolve a 'WI.SymBV' to concrete, if possible. If the 'WI.SymBV' is truly
-- symbolic, this will try to constrain the lower and uppper bounds as much as
-- possible.
resolveSymBV ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , 1 <= w
     , HasCallStack
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> PN.NatRepr w
  -- ^ The bitvector width
  -> WI.SymBV sym w
  -- ^ The symbolic bitvector to concretize
  -> IO (WI.SymBV sym w, ResolveSymBVEffect)
resolveSymBV bak w symBV =
  LCBO.withSolverProcess bak (onlinePanic "resolveSymBV") $ \sp -> do
    let sym = LCB.backendGetSym bak
    resBV <- WURB.resolveSymBV sym WURB.ExponentialSearch w sp symBV
    case resBV of
      WURB.BVConcrete bv -> do
        bv' <- WI.bvLit sym w bv
        pure (bv', Concretized)
      WURB.BVSymbolic d  -> do
        -- NB: Use annotateTerm here to ensure that subsequent What4
        -- simplifications do not rearrange the underlying expression, which
        -- could potentially widen the bounds. There is a chance that not
        -- simplifying the underlying expression could inhibit some potential
        -- optimizations, but we err on the side of having narrower bounds,
        -- which is generally more beneficial for the crucible-llvm memory
        -- model.
        (_, symBV') <- WI.annotateTerm sym $
                       WI.unsafeSetAbstractValue (WUB.BVDArith d) symBV
        pure (symBV', domainToEffect d)
  where
    -- Given a Domain from refinement, determine whether domain was refined or
    -- left unchanged
    domainToEffect :: WUBA.Domain w -> ResolveSymBVEffect
    domainToEffect d =
      case WI.unsignedBVBounds symBV of
        Nothing ->
          case d of
            WUBA.BVDAny _ ->
              -- Bounds were unknown before and after they cover all possible
              -- values.
              UnchangedBounds
            WUBA.BVDInterval mask _ _ | WUBA.ubounds d == (0, mask) ->
              -- Bounds were unknown before and after they cover all possible
              -- values.
              UnchangedBounds
            WUBA.BVDInterval {} -> RefinedBounds
        Just oldBounds | WUBA.ubounds d == oldBounds -> UnchangedBounds
        Just _ -> RefinedBounds

-- | Resolve a 'WI.SymBV' to concrete, if possible. If it is concrete, return
-- it with 'Right'. Otherwise, return an explanation of why concretization
-- failed with 'Left'.
resolveSymBVAs ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , 1 <= w
     , HasCallStack
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> PN.NatRepr w
  -- ^ The bitvector width
  -> WI.SymBV sym w
  -- ^ The symbolic bitvector to concretize
  -> IO (Either ResolutionFailure (BV.BV w))
resolveSymBVAs bak w symBV = resolveSingletonSymbolicAs (concreteBV w) bak symBV

-- | Resolve an 'LCLM.LLVMPtr' to concrete, if possible
--
-- The block id and offset are concretized independently, and either (or
-- neither) could be updated
resolveSingletonPointer
  :: ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , 1 <= w
     , HasCallStack
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> LCLM.LLVMPtr sym w
  -- ^ The symbolic term to concretize
  -> IO (LCLM.LLVMPtr sym w, ResolveSymBVEffect)
resolveSingletonPointer bak (LCLM.LLVMPointer base off) = do
  base' <- resolveSymNat bak base
  (off', effect) <- resolveSymBV bak (WI.bvWidth off) off
  return ((LCLM.LLVMPointer base' off'), effect)
