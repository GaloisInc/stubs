{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Stubs.Common where
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO

-- | Simple data combining an expr builder with its associated solver backend.
-- This helps throughout the codebase, where constraints need to show these are related to do anything useful.
data Sym sym = forall scope st fs solver . (sym ~ WE.ExprBuilder scope st fs,WI.IsExprBuilder sym,WPO.OnlineSolver solver, LCB.IsSymBackend sym (LCBO.OnlineBackend solver scope st fs)) => Sym sym ( LCBO.OnlineBackend solver scope st fs)
