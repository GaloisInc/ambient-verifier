{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Ambient.Property.Record
  ( recordSyscallEvent
  , recordFunctionEvent
  , recordOverrideEvent
  ) where

import           Control.Lens ( (^.), over )
import qualified Data.Foldable as F
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Text as DT

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Types as LCT
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
recordSyscallEvent bak syscallName props oec = recordEvent (matchSyscallEvent syscallName) bak (APD.IssuesSyscall syscallName) props (Just oec)
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
  Maybe (AO.ObservableEventConfig sym) ->
  -- ^ Do not record as an observable event if 'Nothing'.  This option exists
  -- to avoid double reporting of override applications and function calls.
  LCS.SimState p sym ext rtp f args ->
  IO (LCS.SimState p sym ext rtp f args)
recordFunctionEvent bak fnName = recordEvent (matchFunctionEvent fnName) bak (APD.InvokesFunction fnName)
  where
    matchFunctionEvent :: WF.FunctionName -> APD.Transition -> Bool
    matchFunctionEvent expected t =
      case t of
        APD.InvokesFunction name | name == expected -> True
        _ -> False

-- | Record an override application.  Automatically records a function property
-- transition as well.
recordOverrideEvent :: LCB.IsSymBackend sym bak
                    => bak
                    -> WF.FunctionName
                    -- ^ Override's name
                    -> LCT.CtxRepr typs
                    -- ^ Override's argument types
                    -> Ctx.Assignment (LCS.RegEntry sym) typs
                    -- ^ Override's argument values
                    -> Maybe (LCLM.SomePointer sym)
                    -- ^ Override's return value, or 'Nothing' if the override
                    -- does not return anything.
                    -> AET.Properties
                    -> AO.ObservableEventConfig sym
                    -> LCSE.SimState p sym ext rtp f args
                    -> IO (LCSE.SimState p sym ext rtp f args)
recordOverrideEvent bak ovName argTyps args retVal props oec st = do
  let oe = AO.AppliesFunctionOverride ovName
                                      (reverse (extractPtrArgs argTyps args))
                                      retVal
  st' <- recordObservableEvent bak oe oec st
  recordFunctionEvent bak ovName props Nothing st'

  where
    -- Convert a context full of function arguments to a list of pointers.
    -- NOTE: The output list is in the same order as the context, so it contains
    -- the arguments in reverse order.
    extractPtrArgs :: LCT.CtxRepr typs
                   -> Ctx.Assignment (LCS.RegEntry sym) typs
                   -> [ LCLM.SomePointer sym ]
    extractPtrArgs typs argCtx =
      case Ctx.viewAssign typs of
        Ctx.AssignEmpty -> []
        Ctx.AssignExtend typs' typ ->
          case typ of
            LCLM.LLVMPointerRepr _ ->
              let (argCtx', LCS.regValue -> arg) = Ctx.decompose argCtx in
              LCLM.SomePointer arg : extractPtrArgs typs' argCtx'
            _ -> AP.panic AP.Property
                          "recordOverrideEvent"
                          [ "Unexpected function argument type: " ++ show typ ]

-- | Record an observable event
recordObservableEvent ::
  LCB.IsSymBackend sym bak =>
  bak ->
  AO.ObservableEventType ->
  AO.ObservableEventConfig sym ->
  LCS.SimState p sym ext rtp f args ->
  IO (LCS.SimState p sym ext rtp f args)
recordObservableEvent bak event config state = do
  let oeseq = readGlobal (AO.oecGlobal config) state
  let AO.RecordObservableEvent oecRecord = AO.oecRecordFn config
  cond <- LCB.getPathCondition bak
  oeseq' <- oecRecord sym event cond oeseq
  return $ writeGlobal (AO.oecGlobal config) oeseq' state
  where
    sym = LCB.backendGetSym bak

-- | Record a transition
recordEvent ::
  forall p sym ext rtp f args bak.
  LCB.IsSymBackend sym bak =>
  (APD.Transition -> Bool) ->
  bak ->
  APD.Transition ->
  AET.Properties ->
  Maybe (AO.ObservableEventConfig sym) ->
  -- ^ Record an observable event if a config is present
  LCS.SimState p sym ext rtp f args ->
  IO (LCS.SimState p sym ext rtp f args)
recordEvent event bak t props mOec state = do
  state' <-
    maybe (pure state)
          (\oec -> recordObservableEvent bak (AO.Transition t) oec state)
          mOec
  F.foldlM (\state'' (prop, traceGlobal) ->
             do let t0 = readGlobal traceGlobal state''
                t1 <- AET.recordEvent event sym prop t0
                pure $ writeGlobal traceGlobal t1 state'')
           state' (AET.properties props)
  where
    sym = LCB.backendGetSym bak

-- | Read from a global variable
readGlobal ::
  LCS.GlobalVar tp ->
  LCS.SimState p sym ext rtp f args ->
  LCS.RegValue sym tp
readGlobal gv st = do
  let globals = st ^. LCSE.stateTree . LCSE.actFrame . LCS.gpGlobals
  case LCSG.lookupGlobal gv globals of
    Just v  -> v
    Nothing -> AP.panic AP.Property "readGlobal"
                 [ "Failed to find global variable: "
                   ++ show (LCCC.globalName gv) ]

-- | Write to a global variable
writeGlobal ::
  LCS.GlobalVar tp ->
  LCS.RegValue sym tp ->
  LCS.SimState p sym ext rtp f args ->
  LCS.SimState p sym ext rtp f args
writeGlobal gv rv st =
  over (LCSE.stateTree . LCSE.actFrame . LCS.gpGlobals)
       (LCSG.insertGlobal gv rv)
       st
