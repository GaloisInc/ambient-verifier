{-# LANGUAGE ScopedTypeVariables #-}
module Ambient.Property.Record
  ( recordSyscallEvent
  , recordFunctionEvent
  ) where

import           Control.Lens ( (^.), over )
import qualified Data.Foldable as F
import qualified Data.Text as DT

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified What4.FunctionName as WF

import qualified Ambient.EventTrace as AET
import qualified Ambient.ObservableEvents as AO
import qualified Ambient.Panic as AP
import qualified Ambient.Property.Definition as APD

-- | Record a syscall transition
recordSyscallEvent ::
  forall p sym ext rtp f args bak.
  LCB.IsSymBackend sym bak =>
  bak ->
  DT.Text ->
  AET.Properties ->
  AO.ObservableEventConfig sym ->
  LCS.SimState p sym ext rtp f args ->
  IO (LCS.SimState p sym ext rtp f args)
recordSyscallEvent bak syscallName = recordEvent (matchSyscallEvent syscallName) bak (APD.IssuesSyscall syscallName)
  where
    -- | Returns 'True' if the transition is for the named system call
    matchSyscallEvent :: DT.Text -> APD.Transition -> Bool
    matchSyscallEvent expected t =
      case t of
        APD.IssuesSyscall name | name == expected -> True
        _ -> False

-- | Record a function property transition.
recordFunctionEvent ::
  forall p sym ext rtp f args bak.
  LCB.IsSymBackend sym bak =>
  bak ->
  WF.FunctionName ->
  AET.Properties ->
  AO.ObservableEventConfig sym ->
  LCS.SimState p sym ext rtp f args ->
  IO (LCS.SimState p sym ext rtp f args)
recordFunctionEvent bak fnName = recordEvent (matchFunctionEvent fnName) bak (APD.InvokesFunction fnName)
  where
    matchFunctionEvent :: WF.FunctionName -> APD.Transition -> Bool
    matchFunctionEvent expected t =
      case t of
        APD.InvokesFunction name | name == expected -> True
        _ -> False

-- | Record a transition
recordEvent ::
  forall p sym ext rtp f args bak.
  LCB.IsSymBackend sym bak =>
  (APD.Transition -> Bool) ->
  bak ->
  APD.Transition ->
  AET.Properties ->
  AO.ObservableEventConfig sym ->
  LCS.SimState p sym ext rtp f args ->
  IO (LCS.SimState p sym ext rtp f args)
recordEvent event bak t props oec state = do
  let oeseq = readGlobal (AO.oecGlobal oec) state
  let AO.RecordObservableEvent oecRecord = AO.oecRecordFn oec
  cond <- LCB.getPathCondition bak
  oeseq' <- oecRecord sym t cond oeseq
  let state' = writeGlobal (AO.oecGlobal oec) oeseq' state
  F.foldlM (\state'' (prop, traceGlobal) ->
             do let t0 = readGlobal traceGlobal state''
                t1 <- AET.recordEvent event sym prop t0
                pure $ writeGlobal traceGlobal t1 state'')
           state' (AET.properties props)
  where
    sym = LCB.backendGetSym bak

    readGlobal ::
      forall tp.
      LCS.GlobalVar tp ->
      LCS.SimState p sym ext rtp f args ->
      LCS.RegValue sym tp
    readGlobal gv st = do
      let globals = st ^. LCSE.stateTree . LCSE.actFrame . LCS.gpGlobals
      case LCSG.lookupGlobal gv globals of
        Just v  -> v
        Nothing -> AP.panic AP.Property "recordFunctionEvent"
                     [ "Failed to find global variable: "
                       ++ show (LCCC.globalName gv) ]

    writeGlobal ::
      forall tp.
      LCS.GlobalVar tp ->
      LCS.RegValue sym tp ->
      LCS.SimState p sym ext rtp f args ->
      LCS.SimState p sym ext rtp f args
    writeGlobal gv rv st =
      over (LCSE.stateTree . LCSE.actFrame . LCS.gpGlobals)
           (LCSG.insertGlobal gv rv)
           st
