{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE StandaloneDeriving #-}
module Ambient.Diagnostic (
  Diagnostic(..)
  ) where

import qualified Control.Exception as X
import           Control.Lens ( (^.) )
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Data.Time.Clock as DTC
import           Numeric ( showHex )
import qualified Prettyprinter as PP
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.LabeledPred as WL

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.Simulator.SimError as LCSS
import qualified Lang.Crucible.Syntax.Concrete as LCSC

import qualified Ambient.Override.List.Types as AOLT

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
  DisprovedGoal :: (sym ~ WE.ExprBuilder t st fs) => sym -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) LCSS.SimError -> DTC.NominalDiffTime -> Diagnostic
  -- | Execution has reached a Weird Machine at the given address
  ExecutingWeirdMachineAt :: Integer -> Diagnostic
  -- | Setting up the goals for the given property
  AssertingGoalsForProperty :: T.Text -> Maybe T.Text -> Diagnostic
  -- | Executing a user override test
  ExecutingOverrideTest :: LCSC.ACFG ext -> FilePath -> Diagnostic
  -- | Listing the overrides registered for a binary
  ListingOverrides :: AOLT.OverrideLists arch -> Diagnostic

ppSymbol :: (DMM.MemWidth w) => Maybe BSC.ByteString -> DMM.MemSegmentOff w -> String
ppSymbol (Just fnName) addr = show addr ++ " (" ++ BSC.unpack fnName ++ ")"
ppSymbol Nothing addr = show addr

instance PP.Pretty Diagnostic where
  pretty d =
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
          DMD.ReportAnalyzeBlock _ baddr ->
            PP.pretty "Analyzing a block at address " <> PP.pretty baddr <> PP.line
      SolverInteractionEvent verb msg ->
        PP.pretty "Solver response " <> PP.parens (PP.pretty verb) <> PP.pretty ": " <> PP.pretty msg <> PP.line
      GoalTimeout _sym _p ->
        -- FIXME: Add some more detail here, but probably don't print the entire term
        --
        -- It would be nice to be able to provide context in the timeout message
        PP.pretty "Timeout while solving goal" <> PP.line
      ErrorProvingGoal _sym _p exn ->
        PP.pretty "Error while proving goal: " <> PP.viaShow exn <> PP.line
      ProvedGoal _sym _p elapsed ->
        PP.pretty "Proved a goal in " <> PP.viaShow elapsed <> PP.pretty " seconds" <> PP.line
      DisprovedGoal _sym p elapsed ->
        mconcat [ PP.pretty "Disproved a goal in " <> PP.viaShow elapsed <> PP.pretty " seconds" <> PP.line
                , PP.indent 2 (PP.viaShow (p ^. WL.labeledPredMsg)) <> PP.line
                ]
      ExecutingWeirdMachineAt addr ->
        PP.pretty "Execution transferred to a Weird Machine at 0x" <> PP.pretty (showHex addr "") <> PP.line
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
      ListingOverrides (AOLT.OverrideLists{ AOLT.syscallOverrides
                                          , AOLT.functionOverrides
                                          , AOLT.kernelFunctionOverrides
                                          }) ->
        PP.vcat
          [ overridesHeader "Syscall overrides"
            <> foldMap (\(name, num) ->
                         PP.pretty "- " <> PP.pretty name <>
                         PP.pretty " (syscall number " <> PP.pretty num <>
                         PP.pretty ")" <> PP.line)
                       syscallOverrides

          , overridesHeader "Function overrides"
            <> foldMap (\name ->
                         PP.pretty "- " <> PP.pretty name <> PP.line)
                       functionOverrides
            <> foldMap (\(name, addr) ->
                         PP.pretty "- " <> PP.pretty name <>
                         PP.pretty " (kernel function at address " <> PP.pretty addr <>
                         PP.pretty ")" <> PP.line)
                       kernelFunctionOverrides
          ]
    where
      overridesHeader title = PP.vcat
        [ PP.pretty "============================"
        , PP.pretty "== " <> PP.pretty title
        , PP.pretty "============================"
        ] <> PP.line
