{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
module Stubs.Diagnostic (
  Diagnostic(..),
  ppDiagnostic
  ) where

import qualified Control.Exception as X
import           Control.Lens ( (^.) )
import qualified Control.Lens as Lens
import qualified Data.Aeson as DA
import qualified Data.Aeson.Key as DAK
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Data.ByteString.Lazy.Char8 as DBSL
import qualified Data.Time.Clock as DTC
import           Numeric ( showHex )
import qualified Prettyprinter as PP
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.LabeledPred as WL
import qualified What4.ProgramLoc as WP

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.Simulator.SimError as LCSS
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Stubs.Style as STY

data Diagnostic where
  -- | Report an event from the code discovery phase
  --
  -- Note: We may want to enhance this with an indicator of the module being loaded (e.g., a filename)
  DiscoveryEvent :: ( DMM.MemWidth (DMD.ArchAddrWidth arch)
                    , DMC.ArchConstraints arch
                    , w ~ (DMC.RegAddrWidth (DMC.ArchReg arch)) )
                    => DMD.AddrSymMap w
                    -> DMD.DiscoveryEvent arch
                    -> Diagnostic
  -- | A debug message produced by What4 when interacting with a solver during
  -- symbolic execution. This should not be confused with the actual output
  -- from the solver itself, which is a separate thing that What4 logs
  -- independently of its own debug messages.
  --
  -- The 'Int' is the verbosity level associated with the message
  What4SolverDebugEvent :: Int -> String -> Diagnostic
  -- | Timeout while verifying a goal
  GoalTimeout :: (sym ~ WE.ExprBuilder t st fs) => sym -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) LCSS.SimError -> Diagnostic
  -- | An error was raised while verifying a goal
  ErrorProvingGoal :: (sym ~ WE.ExprBuilder t st fs) => sym -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) LCSS.SimError -> X.SomeException -> Diagnostic
  -- | A goal was successfully proved
  ProvedGoal :: (sym ~ WE.ExprBuilder t st fs) => sym -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) LCSS.SimError -> DTC.NominalDiffTime -> Diagnostic
  -- | A goal was disproved with a counterexample
  --
  -- NOTE: We don't currently capture the counterexample; it would need to be
  -- fully grounded here, as the solver connection will be closed by the time we
  -- process the exception
  DisprovedGoal :: (sym ~ WE.ExprBuilder t st fs) => sym -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) LCSS.SimError -> DTC.NominalDiffTime -> Diagnostic
  -- | Execution has reached a Weird Machine at the given address
  ExecutingWeirdMachineAt :: Integer -> Diagnostic
  -- | Setting up the goals for the given property
  AssertingGoalsForProperty :: T.Text -> Maybe T.Text -> Diagnostic
  -- | Executing a user override test
  ExecutingOverrideTest :: LCSC.ACFG ext -> FilePath -> Diagnostic
  -- | Reporting a symbolic branch
  SymbolicBranch :: Maybe WP.ProgramLoc -> Diagnostic
  -- | Invoking a function call in the simulator
  FunctionCall :: DMM.MemWidth w
               => WF.FunctionName
                  -- ^ The function name
               -> DMM.MemWord w
                  -- ^ The address where the function is defined
               -> Maybe (DMM.MemWord w)
                  -- ^ The address that the function returns to (if known)
               -> Diagnostic

ppSymbol :: (DMM.MemWidth w) => Maybe BSC.ByteString -> DMM.MemSegmentOff w -> String
ppSymbol (Just fnName) addr = show addr ++ " (" ++ BSC.unpack fnName ++ ")"
ppSymbol Nothing addr = show addr

instance PP.Pretty Diagnostic where
  -- | The Pretty instance for Diagnostic is for printing plain text to files.
  pretty :: Diagnostic -> PP.Doc ann
  pretty = PP.unAnnotate . ppDiagnostic

-- | Produces an annotated Doc (for colorized ANSI terminal printing),
-- which is not possible with a Pretty instance.
ppDiagnostic :: Diagnostic -> PP.Doc STY.Style
ppDiagnostic d =
  case d of
    DiscoveryEvent symMap de ->
      case de of
        DMD.ReportAnalyzeFunction memOff ->
          PP.pretty "Starting to analyze a function at address " <> PP.pretty memOff <> PP.line
        DMD.ReportAnalyzeFunctionDone memOff ->
          PP.pretty "Finished analyzing a function at address " <> PP.pretty memOff <> PP.line
        DMD.ReportIdentifyFunction _ tgt rsn ->
          PP.hcat [ PP.pretty "Identified a candidate function entry point for function "
                  , PP.pretty (ppSymbol (Map.lookup tgt symMap) tgt)
                  , PP.pretty " because "
                  , PP.pretty (DMD.ppFunReason rsn)
                  , PP.line
                  ]
        DMD.ReportAnalyzeBlock _ baddr _ ->
          PP.pretty "Analyzing a block at address " <> PP.pretty baddr <> PP.line
    What4SolverDebugEvent verb msg ->
      PP.pretty "Solver debug event " <>
      PP.parens (PP.pretty "verbosity" PP.<+> PP.pretty verb) <>
      PP.colon PP.<+> PP.pretty msg <> PP.line
    GoalTimeout _sym p ->
      mconcat [ STY.failure $ PP.pretty "Failure: "
              , PP.pretty "Timeout while solving goal" <> PP.line
              , PP.indent 2 (ppSimErrorLoc p) <> PP.line
              ]
    ErrorProvingGoal _sym p exn ->
      mconcat [ STY.failure $ PP.pretty "Failure: "
              , PP.pretty "Error while proving goal: " <> PP.viaShow exn <> PP.line
              , PP.indent 2 (ppSimErrorLoc p) <> PP.line
              ]
    ProvedGoal _sym p elapsed ->
      mconcat [ STY.success $ PP.pretty "Success: "
              , PP.pretty "Proved a goal in " <> PP.viaShow elapsed <> PP.pretty " seconds" <> PP.line
              , PP.indent 2 (ppSimErrorLoc p) <> PP.line
              ]
    DisprovedGoal _sym p elapsed ->
      mconcat [ STY.failure $ PP.pretty "Failure: "
              , PP.pretty "Disproved a goal in " <> PP.viaShow elapsed <> PP.pretty " seconds" <> PP.line
              , PP.indent 2 (PP.viaShow (p ^. WL.labeledPredMsg)) <> PP.line
              ]
    ExecutingWeirdMachineAt addr ->

      mconcat [ STY.success $ PP.pretty "Success:" <> PP.line
              , PP.pretty "Execution transferred to a Weird Machine at 0x" <> PP.pretty (showHex addr "") <> PP.line ]
    AssertingGoalsForProperty name mdesc ->
      let desc = maybe mempty ((PP.line <>) . PP.pretty) mdesc
      in PP.pretty "Asserting goals for property " <> PP.pretty name <> desc <> PP.line
    ExecutingOverrideTest (LCSC.ACFG _ _ g) path ->
          PP.pretty "Executing override test '"
      <> PP.pretty (LCF.handleName (LCCR.cfgHandle g))
      <> PP.pretty "' in '"
      <> PP.pretty path
      <> PP.pretty "'"
      <> PP.line
    SymbolicBranch maybeLoc ->
      let ppShowMaybe mb =
            case mb of
              Just v  -> show (PP.pretty v)
              Nothing -> "unknown"
      in PP.pretty (DBSL.unpack $ DA.encode $
        DA.object [ DAK.fromString "symbolicBranchFunction" DA..= ppShowMaybe (WP.plFunction <$> maybeLoc)
                  , DAK.fromString "symbolicBranchLocation" DA..= ppShowMaybe (WP.plSourceLoc <$> maybeLoc)
                  ]) <> PP.line
    FunctionCall fnName fnAddr mbRetAddr ->
      PP.pretty "Invoking the" PP.<+> PP.squotes (PP.pretty fnName)
        PP.<+> PP.pretty "function"
        PP.<+> PP.parens (PP.pretty "address" PP.<+> PP.pretty fnAddr)
        PP.<>  foldMap
                  (\retAddr -> PP.pretty ", which returns to address"
                        PP.<+> PP.pretty retAddr)
                  mbRetAddr
        PP.<> PP.line

  where
    -- Print the location of a labeled SimError without printing the entire
    -- SimErrorReason, as the latter is often quite large.
    ppSimErrorLoc :: LCB.LabeledPred pred LCSS.SimError -> PP.Doc a
    ppSimErrorLoc p = ppLoc (p ^. WL.labeledPredMsg . Lens.to LCSS.simErrorLoc)

    ppLoc :: WP.ProgramLoc -> PP.Doc a
    ppLoc loc = PP.pretty (WP.plSourceLoc loc) <>
                PP.pretty ": in the function" PP.<+>
                PP.squotes (PP.pretty (WP.plFunction loc))

