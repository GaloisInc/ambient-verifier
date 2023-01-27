{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
-- | Tools for proving goals generated by the verifier
module Ambient.Verifier.Prove (
    ProofStats(..)
  , proveObligations
  ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent.QSem as CCQ
import qualified Control.Exception as X
import           Control.Lens ( (^.) )
import           Control.Monad ( unless )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.Aeson as DA
import qualified Data.IORef as IORef
import qualified Data.Map as Map
import           Data.Maybe ( isJust )
import qualified Data.MultiSet as MSet
import qualified Data.Time.Clock as DTC
import qualified GHC.Conc as GC
import           GHC.Generics ( Generic )
import qualified Lumberjack as LJ
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.Errors as LCLE
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as LCLEUB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.Partial as LCLMP
import qualified Lang.Crucible.Simulator.SimError as LCSS

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Timeout as AT

-- | Stream logs produced by the SMT solver connection out as diagnostics
--
-- Note that there should not be very many of these unless there is a major
-- system configuration issue
streamLogData
  :: LJ.LogAction IO AD.Diagnostic
  -> WS.LogData
streamLogData logAction =
  WS.LogData { WS.logVerbosity = 3
             , WS.logReason = "Solving Goals"
             , WS.logHandle = Nothing
             , WS.logCallbackVerbose = \level msg -> do
                 LJ.writeLog logAction (AD.What4SolverDebugEvent level msg)
             }

-- | A tag to report when a solver thread has been canceled via a timeout
data ThreadTimeout = ThreadTimeout

-- | The result of a goal proof
data ProofResult =
    Success
 -- ^ The goal was successfully proved
  | Fail
 -- ^ The goal was disproved
  | SolverTimeout
 -- ^ The solver timed out during goal proof
  | Error
 -- ^ An error other than a timeout was experienced during the goal proof
  deriving (Eq, Ord, Show)

-- | Statistics on the results of proving multiple goals
data ProofStats = ProofStats {
    psGoals :: Int
 -- ^ Total number of goals
  , psSuccessfulGoals :: Int
 -- ^ Number of goals successfully proved
  , psFailedGoals :: Int
 -- ^ Number of goals disproved
  , psTimeouts :: Int
 -- ^ Number of goals that ended in a timeout
  , psErrors :: Int
 -- ^ Number of goals that ended in an error other than a timeout
  }
  deriving (Generic)
instance DA.ToJSON ProofStats

zeroProofStats :: ProofStats
zeroProofStats = ProofStats { psGoals = 0
                            , psSuccessfulGoals = 0
                            , psFailedGoals = 0
                            , psTimeouts = 0
                            , psErrors = 0 }

-- | Prove a single goal in a separate thread (respecting the available capabilities)
--
-- This function manages mapping threads to capabilities in a scalable way while
-- also managing per-goal timeouts.
proveOneGoal
  :: ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder t st fs
     )
  => LJ.LogAction IO AD.Diagnostic
  -> sym
  -> WS.SolverAdapter st
  -- ^ The solver adapter to use to prove the goal
  -> IORef.IORef [CCA.Async ProofResult]
  -- ^ The collection of pending worker threads
  -> CCQ.QSem
  -- ^ A count of available capabilities, which will block workers until
  -- capabilities become available to avoid swamping the system
  -> LCB.Assumptions sym
  -- ^ Assumptions in scope for this goal
  -> LCB.LabeledPred (WE.Expr t WI.BaseBoolType) LCSS.SimError
  -- ^ The goal to prove
  -> AT.Timeout
  -- ^ The solver timeout for proving the goal
  -> IO ()
proveOneGoal logAction sym adapter workers sem assumptionsInScope p timeoutDuration = do
  -- We spawn a thread that waits until there is an available capability
  --
  -- That thread implements the timeout logic and invokes the solver under that timeout
  --
  -- The bracket ensures that the capability is always returned
  timeoutWrapper <- CCA.async (X.bracket_ (CCQ.waitQSem sem) (CCQ.signalQSem sem) spawnWorker)

  -- Save the handle to the outer thread so that we can wait on them all later
  --
  -- Using an IORef is safe here because the traversal of the Goals structure is
  -- serialized (only the solver executions are concurrent).
  IORef.modifyIORef' workers (timeoutWrapper:)
  where
    -- The actual worker races the solver thread against a timeout thread
    spawnWorker = do
      worker <- CCA.async $ do
        assumptions <- LCB.assumptionsPred sym assumptionsInScope
        goal <- WI.notPred sym (p ^. LCB.labeledPred)
        t0 <- DTC.getCurrentTime
        WS.solver_adapter_check_sat adapter sym (streamLogData logAction) [assumptions, goal] $ \satRes -> do
          t1 <- DTC.getCurrentTime
          case satRes of
            WS.Unsat {} -> do
              LJ.writeLog logAction (AD.ProvedGoal sym p (t1 `DTC.diffUTCTime` t0))
              return Success
            WS.Unknown -> do
              LJ.writeLog logAction (AD.GoalTimeout sym p)
              return SolverTimeout
            WS.Sat _model -> do
              LJ.writeLog logAction (AD.DisprovedGoal sym p (t1 `DTC.diffUTCTime` t0))
              return Fail
      timeout <- CCA.async $ do
        CC.threadDelay (AT.microsAsInt (AT.timeoutAsMicros timeoutDuration))
        CCA.cancel worker
        return ThreadTimeout

      -- Wait for the worker to finish, or cancel it after a timeout
      res <- CCA.waitEitherCatch worker timeout
      case res of
        Right (Right ThreadTimeout) -> do
          LJ.writeLog logAction (AD.GoalTimeout sym p)
          return SolverTimeout
        Right (Left exn) -> do
          LJ.writeLog logAction (AD.ErrorProvingGoal sym p exn)
          return Error
        Left (Left exn) -> do
          LJ.writeLog logAction (AD.ErrorProvingGoal sym p exn)
          return Error
        Left (Right proofResult) -> return proofResult

-- | Prove all of the obligations generated during symbolic execution
--
-- This extracts the goals tree from the symbolic backend (@sym@) and traverses
-- the structure to prove each goal.
--
-- Returns the number of goals
--
-- NOTE: This solves goals in parallel using an offline solver (i.e., the
-- 'WS.SolverAdapter'), which means that it spawns a fresh solver instance for
-- each goal.
proveObligations
  :: (LCB.IsSymBackend sym bak, sym ~ WE.ExprBuilder t st fs, MonadIO m)
  => LJ.LogAction IO AD.Diagnostic
  -> bak
  -> WS.SolverAdapter st
  -> AT.Timeout
  -> LCLM.LLVMAnnMap sym
  -> m ProofStats
proveObligations logAction bak adapter timeoutDuration badBehaviors = do
  mobligations <- liftIO (LCB.getProofObligations bak)
  case mobligations of
    Nothing -> return zeroProofStats
    Just obligations -> do
      workersRef <- liftIO $ IORef.newIORef []
      caps <- liftIO GC.getNumCapabilities
      sem <- liftIO (CCQ.newQSem caps)

      -- Traverse the proof obligations and spawn off threads to attempt to prove them
      go workersRef sem mempty obligations

      -- Block until all of the workers finish (possibly by timing out)
      workers <- liftIO $ IORef.readIORef workersRef
      proofResults <- liftIO $ mapM CCA.wait workers
      let prSet = MSet.fromList proofResults
      return $ ProofStats { psGoals = MSet.size prSet
                          , psSuccessfulGoals = MSet.occur Success prSet
                          , psFailedGoals = MSet.occur Fail prSet
                          , psTimeouts = MSet.occur SolverTimeout prSet
                          , psErrors = MSet.occur Error prSet }
  where
    sym = LCB.backendGetSym bak

    go workers sem assumptionsInScope goals =
      case goals of
        LCB.Assuming asumps childGoals ->
          go workers sem (asumps <> assumptionsInScope) childGoals
        LCB.ProveConj children1 children2 -> do
          go workers sem assumptionsInScope children1
          go workers sem assumptionsInScope children2
        LCB.Prove p ->
          -- Prove a goal, unless it is a check for an undefined behavior that
          -- we wish to elide, in which case we skip it.
          -- See Note [Undefined behavior and machine code].
          unless (isElidedUndefinedBehaviorPred p)
            (liftIO $ proveOneGoal logAction sym adapter workers sem assumptionsInScope p timeoutDuration)

    -- Check whether a predicate is annotated as an undefined behavior check
    -- that we wish to elide in the verifier.
    -- See Note [Undefined behavior and machine code].
    isElidedUndefinedBehaviorPred p = isJust $ do
      ann <- WI.getAnnotation sym (p ^. LCB.labeledPred)
      (_, badBehavior) <- Map.lookup (LCLMP.BoolAnn ann) badBehaviors
      case badBehavior of
        LCLE.BBUndefinedBehavior ub ->
          case ub of
            LCLEUB.FreeBadOffset{}   -> Nothing
            LCLEUB.FreeUnallocated{} -> Nothing
            LCLEUB.DoubleFree{}      -> Nothing
            _                        -> Just ()
        LCLE.BBMemoryError{}         -> Nothing

{-
Note [Undefined behavior and machine code]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The verifier uses Crucible's LLVM memory model to reason about the behavior of
machine code. While the semantics of LLVM correspond to that of machine code in
many ways, there are also some awkward discrepancies. For instance, the LLVM
memory model is very careful to throw failing assertions for things that would
constitute undefined behavior in C, but these do not always correspond to
undefined behavior at the machine code level.

As an example, consider the undefined behavior demonstrated in the X86_64
sprintf_bof test's exploit. This exploit overwrites the lower 4 bytes of a
stored return address and leaves the upper 4 bytes untouched. The resulting
pointer is therefore a combination of 2 writes, which triggers a failing
undefined behavior check in the LLVM memory model.

Although this behavior may be undefined at the C level, it has defined
semantics at the X86_64 binary level. Because many exploits rely on C level
undefined behavior, we simply elide most of these checks. The
`isElidedUndefinedBehaviorPred` function detects checks of this sort by looking
for the BBUndefinedBehavior class of BadBehavior.

While we elide most of the LLVM memory model's undefined behavior checks, we do
make special exceptions for some of them. In particular, the built-in free
override can exhibit undefined behavior if a program performs a double-free or
a use-after-free error. These are arguably just as bad at the machine code
level as they are at the C level (some binary exploits might even be triggered
by these undefined uses of free!), so we do /not/ elide these checks.

Ultimately, there is not a single set of guidelines that governs whether an
undefined behavior check should be elided or not. If a class of undefined
behavior makes sense at the machine code level, then it could be worth catching
in the verifier. Determining what does or does not make sense at the machine
code level is ultimately a judgment call, however.
-}
