module Stubs.MonadState
  ( modifyM
  , stateM
  ) where

import qualified Control.Monad.State as CMS

-- | Given a function that modifies state and returns a new value, this
-- function wraps the call in @get@ and @put@ operations to update the state in
-- the state monad.
modifyM :: CMS.MonadState s m => (s -> m (a, s)) -> m a
modifyM fn = do
  s <- CMS.get
  (a, s') <- fn s
  CMS.put s'
  return a

-- | Given a function that modifies state, this function wraps the call in
-- @get@ and @put@ operations to update the state in the state monad.
stateM :: CMS.MonadState s m => (s -> m s) -> m ()
stateM fn = do
  s <- CMS.get
  s' <- fn s
  CMS.put s'
