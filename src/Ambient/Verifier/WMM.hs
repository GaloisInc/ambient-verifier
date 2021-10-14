{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | The Weird Machine Monitor (WMM), which identifies when execution transfers
-- to a Weird Machine (from normal execution)
module Ambient.Verifier.WMM (
    WMMCallback(..)
  , WMMCallbackResult(..)
  , WMConfig(..)
  , initWMConfig
  , wmmFeature
  ) where

import           Control.Lens ( (^.), set )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Text as DT
import qualified Lumberjack as LJ
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.SatResult as WSR
import qualified What4.Solver as WS

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.CallFrame as LCSC
import qualified Lang.Crucible.Simulator.EvalStmt as LCSEv
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Simulator.SymSequence as LCSS
import qualified Lang.Crucible.Types as LCT

import qualified Ambient.Diagnostic as AD
import qualified Ambient.EventTrace as AE
import qualified Ambient.Panic as AP
import qualified Ambient.Property.Definition as APD
import qualified Ambient.Solver as AS

-- | A WMMCallbackResult represents the possible outcomes from executing a
-- WMMCallback
data WMMCallbackResult p sym arch f a =
    -- Weird machine execution is complete and symbolic execution should end
    -- and propagate the 'ExecResult' up
    WMMResultCompleted (LCSE.ExecResult p
                                        sym
                                        (DMS.MacawExt arch)
                                        (LCS.RegEntry sym (DMS.ArchRegStruct arch)))

  -- Symbolic execution should continue with a new 'SimState'
  | WMMResultNewState (LCSE.SimState p
                                     sym
                                     (DMS.MacawExt arch)
                                     (LCS.RegEntry sym (DMS.ArchRegStruct arch))
                                     f
                                     a)

  -- No changes should be made
  | WMMResultNoChange

-- | A WMConfig contains global variables tracking properties of the weird
-- machines in an execution
newtype WMConfig =
  WMConfig { wmProperties :: AE.Properties
           -- ^ A mapping of properties to verify, to their corresponding global
           -- variables holding symbolic traces
           }

-- | Build an initial 'WMConfig' with all booleans set to 'False'.  Returns a
-- 'WMConfig' and an updated global state.
initWMConfig :: ( WI.IsExprBuilder sym )
             => sym
             -> LCF.HandleAllocator
             -> LCSG.SymGlobalState sym
             -- ^ Global state to insert globals into
             -> [APD.Property APD.StateID]
             -- ^ The properties to verify, for which we need to allocate
             -- verifier globals
             -> IO (WMConfig, LCSG.SymGlobalState sym)
initWMConfig sym halloc globals0 props = do
  let pleatM seed xs f = F.foldlM f seed xs
  (globals1, props') <- pleatM (globals0, []) props $ \(gs, ps) p -> do
    let varName = DT.pack "AMBIENT_EventTrace_" <> APD.propertyName p
    traceGlob <- LCCC.freshGlobalVar halloc varName AE.eventTraceRepr
    emptyTrace <- LCSS.nilSymSequence sym
    -- Always start each trace in the initial state
    s0 <- WI.intLit sym (APD.stateID (APD.initialState p))
    initialTrace <- LCSS.consSymSequence sym s0 emptyTrace
    return (LCSG.insertGlobal traceGlob initialTrace gs, (p, traceGlob) : ps)
  return (WMConfig (AE.Properties props'), globals1)


-- | This action is run when execution reaches a Weird Machine entry
--
-- It could be used to launch a subsequent symbolic execution process to explore
-- the behavior of the Weird Machine. The callback is passed:
--
--   1. The address of the Weird Machine entry point
--   2. The entire symbolic execution state at the start of the Weird Machine
newtype WMMCallback arch sym where
  WMMCallback :: (forall p f a . Integer -> LCSE.SimState p sym (DMS.MacawExt arch) (LCS.RegEntry sym (DMS.ArchRegStruct arch)) f a -> IO (WMMCallbackResult p sym arch f a)) -> WMMCallback arch sym

-- | The SMT interaction logger
smtLogger :: LJ.LogAction IO AD.Diagnostic -> WS.LogData
smtLogger logAction =
  WS.defaultLogData { WS.logCallbackVerbose = doLog }
  where
    doLog verb msg =
      LJ.writeLog logAction (AD.SolverInteractionEvent verb msg)

-- | Look up a global that we really require to already be in the global state
--
-- It is a programming error in the verifier if it is not, so panic if it is not
-- present
lookupGlobal
  :: LCS.GlobalVar tp
  -> LCSG.SymGlobalState sym
  -> IO (LCS.RegValue sym tp)
lookupGlobal gv globState =
  case LCSG.lookupGlobal gv globState of
    Nothing -> AP.panic AP.WMM
                 "handleControlTransfer"
                 ["Missing expected global variable binding: " ++ show gv]
    Just val -> return val

matchWeirdEntry :: Integer -> APD.Transition -> Bool
matchWeirdEntry thisAddr t =
  case t of
    APD.EnterWeirdMachine transitionAddr -> toInteger transitionAddr == thisAddr
    _ -> False

-- | At a control transfer, inspect the current register state (the
-- 'LCS.RegEntry' that contains the full symbolic register file) and determine
-- if it is one of the target Weird Machine addresses provided.
--
-- Note that in general, this test is symbolic and requires an SMT solver to
-- resolve (hence, we pass in a 'WS.SolverAdapter' to let us issue SMT
-- queries. FIXME: This can be expensive, so we should add a fast mode that does
-- syntactic checks instead.
--
-- See Note [IP Matching] for details on these conditions
handleControlTransfer
  :: forall arch ext p sym rtp f a tp t st fs
   . ( ext ~ DMS.MacawExt arch
     , LCCE.IsSyntaxExtension ext
     , DMS.SymArchConstraints arch
     , LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder t st fs
     , rtp ~ LCS.RegEntry sym (DMS.ArchRegStruct arch)
     )
  => LJ.LogAction IO AD.Diagnostic
  -> WS.SolverAdapter st
  -- ^ The solver adapter to use for checking IP values
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -> AE.Properties
  -- ^ The properties that the verifier should check (and the globals capturing their traces)
  -> WMMCallback arch sym
  -- ^ The action to run when a Weird Machine is encountered
  -> LCS.RegEntry sym tp
  -- ^ The current register state
  -> LCSE.SimState p sym ext rtp f a
  -- ^ The current simulator state (to be passed to the 'WMMCallback' if a Weird Machine is entered)
  -> LCS.ExecState p sym ext rtp
  -- ^ The current execution state
  -> IO (LCSEv.ExecutionFeatureResult p sym ext rtp)
handleControlTransfer logAction adapter archVals props (WMMCallback action) regState st estate
  | Just PC.Refl <- PC.testEquality regsRepr (LCS.regType regState) = do
      case LCS.regValue (DMS.lookupReg archVals regState DMC.ip_reg) of
        LCLM.LLVMPointer _region ipVal -> do
          mst <- go ipVal (fmap toInteger wmEntries)
          case mst of
            Nothing -> return LCSEv.ExecutionFeatureNoChange
            Just (result, st') ->
              case result of
                WMMResultCompleted completedResult ->
                  return $ LCSEv.ExecutionFeatureNewState (LCSE.ResultState completedResult)
                WMMResultNoChange -> do
                  -- No change from callback, but need to update SimState to
                  -- capture change to 'hitWm'
                  let estate' = case estate of
                                  LCSE.CallState ret call state ->
                                    -- Here we are copying over all of the event
                                    -- traces from the Weird Machine excursion
                                    -- (otherwise, we lose their updates).
                                    --
                                    -- We have to do this copy because we can't
                                    -- just use the state from the excursion, as
                                    -- type variables don't line up
                                    let globals0 = state ^. LCSE.stateGlobals
                                        copyVariable globs (p, gv) =
                                          case LCSG.lookupGlobal gv (st' ^. LCSE.stateGlobals) of
                                            Nothing -> AP.panic AP.WMM "handleControlTransfer" ["Missing global for property " <> show (APD.propertyName p)]
                                            Just rv -> LCSG.insertGlobal gv rv globs
                                        globals1 = F.foldl' copyVariable globals0 (AE.properties props)
                                        state' = set LCSE.stateGlobals globals1 state
                                    in LCSE.CallState ret call state'
                                  LCSE.TailCallState v r _ ->
                                    LCSE.TailCallState v r st'
                                  LCSE.ReturnState f v r _ ->
                                    LCSE.ReturnState f v r st'
                                  _ -> AP.panic AP.WMM
                                                "handleControlTransfer"
                                                ["Encountered unexpected ExecState type"]
                  return $ LCSEv.ExecutionFeatureModifiedState estate'
                WMMResultNewState _st' ->
                  -- We would like it to be the case that the callback could
                  -- return a modified state that we could resume with. That
                  -- isn't impossible, but we have to carefully consider how we
                  -- want to create a new 'ExecState'
                  AP.panic AP.WMM
                           "handleControlTransfer"
                           ["WMMResultNewState is not currenlty supported"]
  | otherwise = do
      -- FIXME: Emit a log or warning here
      return LCSEv.ExecutionFeatureNoChange
  where
    wmEntries = [ e
                | (p, _gv) <- AE.properties props
                , e <- F.toList (APD.weirdMachineEntries p)
                ]
    regsRepr = LCT.StructRepr (DMS.crucArchRegTypes (DMS.archFunctions archVals))
    sym = st ^. LCSE.stateContext . LCSE.ctxSymInterface
    go :: WI.SymBV sym (DMC.ArchAddrWidth arch) -> [Integer] -> IO (Maybe (WMMCallbackResult p sym arch f a, LCSE.SimState p sym ext rtp f a))
    go _ [] = return Nothing
    go ipVal (wmEntry : rest) = do
      targetBV <- WI.bvLit sym PN.knownNat (BVS.mkBV PN.knownNat wmEntry)
      ipEqTarget <- WI.bvEq sym ipVal targetBV
      goal <- WI.notPred sym ipEqTarget
      let logData = smtLogger logAction
      WS.solver_adapter_check_sat adapter sym logData [goal] $ \sr ->
        case sr of
          WSR.Unsat {} -> do
            LJ.writeLog logAction (AD.ExecutingWeirdMachineAt wmEntry)
            let globs = st ^. LCSE.stateGlobals
            let pleatM seed xs f = F.foldlM f seed xs
            globs' <- pleatM globs (AE.properties props) $ \theseGlobals (prop, eventTraceGlob) -> do
              currentTrace <- lookupGlobal eventTraceGlob theseGlobals
              nextTrace <- AE.recordEvent (matchWeirdEntry wmEntry) sym prop currentTrace
              return (LCSG.insertGlobal eventTraceGlob nextTrace theseGlobals)
            let st' = set LCSE.stateGlobals globs' st
            -- FIXME: The action probably needs to return an updated state, as
            -- it will have continued execution on its own
            result <- action wmEntry st'
            return $ Just (result, st')
          _ -> go ipVal rest


-- | This execution feature observes all control flow transfers and halts
-- execution when it does (so that a separate verification of the Weird Machine
-- can be started).
--
-- It supports observing return-oriented programs and call-oriented programs by
-- inspecting the instruction pointer at each step to see if the control flow
-- target is one of the indicated Weird Machines.
--
-- FIXME: This could also address jump-oriented programs by handling the
-- 'LCSE.ControlTransferState'
wmmFeature
  :: forall arch ext p sym rtp t st fs
   . ( ext ~ DMS.MacawExt arch
     , LCCE.IsSyntaxExtension ext
     , DMS.SymArchConstraints arch
     , LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder t st fs
     , rtp ~ LCS.RegEntry sym (DMS.ArchRegStruct arch)
     )
  => LJ.LogAction IO AD.Diagnostic
  -> AS.Solver
  -- ^ The solver to use when checking the current IP
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -- ^ A property to check, from which weird Machine entry points can be derived
  -> WMMCallback arch sym
  -- ^ An action to run when a Weird Machine is recognized
  -> AE.Properties
  -- ^ The properties to verify, along with the globals capturing their symbolic traces
  -> LCSEv.ExecutionFeature p sym ext rtp
wmmFeature logAction solver archVals action props = LCSEv.ExecutionFeature $ \estate ->
  case estate of
    LCSE.ResultState {} -> return LCSEv.ExecutionFeatureNoChange
    LCSE.AbortState {} -> return LCSEv.ExecutionFeatureNoChange
    LCSE.UnwindCallState {} -> return LCSEv.ExecutionFeatureNoChange
    LCSE.RunningState {} -> return LCSEv.ExecutionFeatureNoChange
    LCSE.SymbolicBranchState {} -> return LCSEv.ExecutionFeatureNoChange
    LCSE.ControlTransferState {} -> return LCSEv.ExecutionFeatureNoChange
    LCSE.OverrideState {} -> return LCSEv.ExecutionFeatureNoChange
    LCSE.BranchMergeState {} -> return LCSEv.ExecutionFeatureNoChange
    LCSE.InitialState {} -> return LCSEv.ExecutionFeatureNoChange
    LCSE.CallState _ (LCSE.CrucibleCall _ cf) st ->
      case LCS.regMap (cf ^. LCSC.frameRegs) of
        Ctx.Empty Ctx.:> regs -> handleControlTransfer logAction (AS.offlineSolver solver) archVals props action regs st estate
        _ -> return LCSEv.ExecutionFeatureNoChange
    LCSE.CallState _ _ _ -> return LCSEv.ExecutionFeatureNoChange
    LCSE.TailCallState _ (LCSE.CrucibleCall _ cf) st ->
      case LCS.regMap (cf ^. LCSC.frameRegs) of
        Ctx.Empty Ctx.:> regs -> handleControlTransfer logAction (AS.offlineSolver solver) archVals props action regs st estate
        _ -> return LCSEv.ExecutionFeatureNoChange
    LCSE.TailCallState _ _ _ -> return LCSEv.ExecutionFeatureNoChange
    LCSE.ReturnState _ _ retRegEntry st ->
      handleControlTransfer logAction (AS.offlineSolver solver) archVals props action retRegEntry st estate


{- Note [IP Matching]

In 'handleControlTransfer', we want to only hook execution if the target of the
control transfer is in our list of Weird Machine entry points. To determine
this, we inspect the instruction pointer in the register file.  We don't
necessarily know which memory region the IP points to (it depends on how macaw
loaded the binary, and especially if it was a Position Independent Executable).

At the very least, we are checking here to ensure that the region is concrete.
Then we make sure that the offset matches one of the prescribed addresses. It
should be the case that any region with code should cover the entire address space.

Note that this may get a lot more complicated with shared libraries and we may
need to actually check the region of the instruction pointer. In those cases,
gadgets may come from both shared libraries and the application itself, so we
will need to be careful to support that once we have examples.

-}
