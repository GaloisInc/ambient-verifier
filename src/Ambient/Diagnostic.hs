{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Ambient.Diagnostic (
  Diagnostic(..)
  ) where

import qualified Control.Exception as X
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map as Map
import qualified Data.Time.Clock as DTC
import qualified Prettyprinter as PP
import qualified What4.Expr as WE
import qualified What4.Interface as WI

import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM

import qualified Lang.Crucible.Backend as LCB

data Diagnostic where
  -- | Report an event from the code discovery phase
  --
  -- Note: We may want to enhance this with an indicator of the module being loaded (e.g., a filename)
  DiscoveryEvent :: (DMM.MemWidth w) => DMD.AddrSymMap w -> DMD.DiscoveryEvent w -> Diagnostic
  -- | A solver interaction event generated during symbolic execution
  --
  -- The 'Int' is the verbosity level associated with the message
  SolverInteractionEvent :: Int -> String -> Diagnostic
  -- | Timeout while verifying a goal
  GoalTimeout :: (sym ~ WE.ExprBuilder t st fs) => sym -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) msg -> Diagnostic
  -- | An error was raised while verifying a goal
  ErrorProvingGoal :: (sym ~ WE.ExprBuilder t st fs) => sym -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) msg -> X.SomeException -> Diagnostic
  -- | A goal was successfully proved
  ProvedGoal :: (sym ~ WE.ExprBuilder t st fs) => sym -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) msg -> DTC.NominalDiffTime -> Diagnostic
  -- | A goal was disproved with a counterexample
  --
  -- NOTE: We don't currently capture the counterexample; it would need to be
  -- fully grounded here, as the solver connection will be closed by the time we
  -- process the exception
  DisprovedGoal :: (sym ~ WE.ExprBuilder t st fs) => sym -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) msg -> DTC.NominalDiffTime -> Diagnostic

ppSymbol :: (DMM.MemWidth w) => Maybe BSC.ByteString -> DMM.MemSegmentOff w -> String
ppSymbol (Just fnName) addr = show addr ++ " (" ++ BSC.unpack fnName ++ ")"
ppSymbol Nothing addr = show addr

instance PP.Pretty Diagnostic where
  pretty d =
    case d of
      DiscoveryEvent symMap de ->
        case de of
          DMD.ReportAnalyzeFunction memOff ->
            PP.pretty "Starting to analyze a function at address " <> PP.pretty memOff
          DMD.ReportAnalyzeFunctionDone memOff ->
            PP.pretty "Finished analyzing a function at address " <> PP.pretty memOff
          DMD.ReportIdentifyFunction _ tgt rsn ->
            PP.hcat [ PP.pretty "Identified a candidate function entry point for function "
                    , PP.pretty (ppSymbol (Map.lookup tgt symMap) tgt)
                    , PP.pretty " because "
                    , PP.pretty (DMD.ppFunReason rsn)
                    ]
          DMD.ReportAnalyzeBlock _ baddr ->
            PP.pretty "Analyzing a block at address " <> PP.pretty baddr
      SolverInteractionEvent verb msg ->
        PP.pretty "Solver response " <> PP.parens (PP.pretty verb) <> PP.pretty ": " <> PP.pretty msg
      GoalTimeout _sym _p ->
        -- FIXME: Add some more detail here, but probably don't print the entire term
        --
        -- It would be nice to be able to provide context in the timeout message
        PP.pretty "Timeout while solving goal"
      ErrorProvingGoal _sym _p exn ->
        PP.pretty "Error while proving goal: " <> PP.viaShow exn
      ProvedGoal _sym _p elapsed ->
        PP.pretty "Proved a goal in " <> PP.viaShow elapsed <> PP.pretty " seconds"
      DisprovedGoal _sym _p elapsed ->
        PP.pretty "Disproved a goal in " <> PP.viaShow elapsed <> PP.pretty " seconds"
