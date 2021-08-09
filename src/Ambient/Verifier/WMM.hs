{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | The Weird Machine Monitor (WMM), which identifies when execution transfers
-- to a Weird Machine (from normal execution)
module Ambient.Verifier.WMM (
    WMMCallback(..)
  , wmmFeature
  ) where

import           Control.Lens ( (^.) )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Set as Set
import           Data.Word ( Word64 )
import qualified Lumberjack as LJ
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.SatResult as WSR
import qualified What4.Solver as WS

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.CallFrame as LCSC
import qualified Lang.Crucible.Simulator.EvalStmt as LCSEv
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Types as LCT

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Solver as AS

-- | This action is run when execution reaches a Weird Machine entry
--
-- It could be used to launch a subsequent symbolic execution process to explore
-- the behavior of the Weird Machine. The callback is passed:
--
--   1. The address of the Weird Machine entry point
--   2. The entire symbolic execution state at the start of the Weird Machine
newtype WMMCallback where
  WMMCallback :: (forall p sym ext rtp f a . Integer -> LCSE.SimState p sym ext rtp f a -> IO (LCSE.SimState p sym ext rtp f a)) -> WMMCallback

-- | The SMT interaction logger
smtLogger :: LJ.LogAction IO AD.Diagnostic -> WS.LogData
smtLogger logAction =
  WS.defaultLogData { WS.logCallbackVerbose = doLog }
  where
    doLog verb msg =
      LJ.writeLog logAction (AD.SolverInteractionEvent verb msg)

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
     )
  => LJ.LogAction IO AD.Diagnostic
  -> WS.SolverAdapter st
  -- ^ The solver adapter to use for checking IP values
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -> Set.Set Integer
  -- ^ Target weird machine addresses
  -> WMMCallback
  -- ^ The action to run when a Weird Machine is encountered
  -> LCS.RegEntry sym tp
  -- ^ The current register state
  -> LCSE.SimState p sym ext rtp f a
  -- ^ The current simulator state (to be passed to the 'WMMCallback' if a Weird Machine is entered)
  -> IO (LCSEv.ExecutionFeatureResult p sym ext rtp)
handleControlTransfer logAction adapter archVals wmEntries (WMMCallback action) regState st
  | Just PC.Refl <- PC.testEquality regsRepr (LCS.regType regState) = do
      case LCS.regValue (DMS.lookupReg archVals regState DMC.ip_reg) of
        LCLM.LLVMPointer _region ipVal -> do
          mst <- go ipVal (F.toList wmEntries)
          case mst of
            Nothing -> return LCSEv.ExecutionFeatureNoChange
            Just _st' -> do
              -- We would like it to be the case that the callback could return
              -- a modified state that we could resume with. That isn't
              -- impossible, but we have to carefully consider how we want to
              -- create a new 'ExecState'
              --
              -- (LCSEv.ExecutionFeatureNewState st')
              return LCSEv.ExecutionFeatureNoChange
  | otherwise = do
      -- FIXME: Emit a log or warning here
      return LCSEv.ExecutionFeatureNoChange
  where
    regsRepr = LCT.StructRepr (DMS.crucArchRegTypes (DMS.archFunctions archVals))
    go :: WI.SymBV sym (DMC.ArchAddrWidth arch) -> [Integer] -> IO (Maybe (LCSE.SimState p sym ext rtp f a))
    go _ [] = return Nothing
    go ipVal (wmEntry : rest) = do
      let sym = st ^. LCSE.stateContext . LCSE.ctxSymInterface
      targetBV <- WI.bvLit sym PN.knownNat (BVS.mkBV PN.knownNat wmEntry)
      ipEqTarget <- WI.bvEq sym ipVal targetBV
      goal <- WI.notPred sym ipEqTarget
      let logData = smtLogger logAction
      WS.solver_adapter_check_sat adapter sym logData [goal] $ \sr ->
        case sr of
          WSR.Unsat {} -> do
            LJ.writeLog logAction (AD.ExecutingWeirdMachineAt wmEntry)
            Just <$> action wmEntry st
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
     )
  => LJ.LogAction IO AD.Diagnostic
  -> AS.Solver
  -- ^ The solver to use when checking the current IP
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -> [Word64]
  -- ^ Weird Machine entry points
  -> WMMCallback
  -- ^ An action to run when a Weird Machine is recognized
  -> LCSEv.ExecutionFeature p sym ext rtp
wmmFeature logAction solver archVals wmEntries action = LCSEv.ExecutionFeature $ \estate ->
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
        Ctx.Empty Ctx.:> regs -> handleControlTransfer logAction (AS.offlineSolver solver) archVals entryInts action regs st
        _ -> return LCSEv.ExecutionFeatureNoChange
    LCSE.CallState _ _ _ -> return LCSEv.ExecutionFeatureNoChange
    LCSE.TailCallState _ (LCSE.CrucibleCall _ cf) st ->
      case LCS.regMap (cf ^. LCSC.frameRegs) of
        Ctx.Empty Ctx.:> regs -> handleControlTransfer logAction (AS.offlineSolver solver) archVals entryInts action regs st
        _ -> return LCSEv.ExecutionFeatureNoChange
    LCSE.TailCallState _ _ _ -> return LCSEv.ExecutionFeatureNoChange
    LCSE.ReturnState _ _ retRegEntry st ->
      handleControlTransfer logAction (AS.offlineSolver solver) archVals entryInts action retRegEntry st
  where
    entryInts = Set.fromList (map toInteger wmEntries)


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
