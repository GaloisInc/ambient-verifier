{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | The main entry point of the AMBIENT binary verifier
module Ambient.Verifier (
    ProgramInstance(..)
  , Metrics(..)
  , verify
  , buildRecordLLVMAnnotation
  ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Control.Exception as X
import           Control.Lens ( (^.), Identity )
import           Control.Monad ( void )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.Aeson as DA
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import           Data.IORef ( IORef, newIORef, modifyIORef', readIORef )
import qualified Data.Map as Map
import           Data.Maybe ( catMaybes, isJust )
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Set as Set
import qualified Data.Text as DT
import qualified Data.Time.Clock as DTC
import qualified Data.Traversable as Trav
import           Data.Word ( Word64 )
import           GHC.Generics ( Generic )
import           GHC.Stack ( HasCallStack )
import qualified Lumberjack as LJ
import qualified System.Directory as Dir
import qualified System.FilePath as FP

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.Errors as LCLE
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.CallStack as LCLMC
import qualified Lang.Crucible.LLVM.MemModel.Partial as LCLMP
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.BoundedExec as LCSBE
import qualified Lang.Crucible.Simulator.BoundedRecursion as LCSBR
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Simulator.PathSatisfiability as LCSP
import qualified Lang.Crucible.Simulator.Profiling as LCSProf
import qualified Lang.Crucible.Simulator.SimError as LCSS
import qualified Lang.Crucible.Simulator.SymSequence as LCSS
import qualified What4.Config as WConf
import qualified What4.Concrete as WC
import qualified What4.Interface as WI
import qualified What4.Partial as WP

import qualified Ambient.Diagnostic as AD
import qualified Ambient.EntryPoint as AEp
import qualified Ambient.EnvVar as AEnv
import qualified Ambient.EventTrace as AEt
import qualified Ambient.Exception as AE
import qualified Ambient.Extensions as AExt
import qualified Ambient.FunctionOverride.Extension as AFE
import qualified Ambient.Loader as AL
import qualified Ambient.ObservableEvents as AO
import qualified Ambient.Panic as AP
import qualified Ambient.Profiler.EmbeddedData as APE
import qualified Ambient.Property.Definition as APD
import qualified Ambient.Solver as AS
import qualified Ambient.Timeout as AT
import qualified Ambient.Verifier.Prove as AVP
import qualified Ambient.Verifier.SymbolicExecution as AVS
import qualified Ambient.Verifier.WME as AVWme
import qualified Ambient.Verifier.WMM as AVW

-- | A definition of the initial state of a program to be verified
--
-- Currently, this just defines the /concrete/ initial state of the
-- program. This will be extended later to support explicitly symbolic initial
-- states.
data ProgramInstance =
  ProgramInstance { piPath :: FilePath
                  -- ^ The path to the binary on disk (or a synthetic name)
                  , piBinary :: BS.ByteString
                  -- ^ The contents of the binary to verify, which will be
                  -- parsed and lifted into the verification IR
                  , piFsRoot :: Maybe FilePath
                  -- ^ Path to the symbolic file system.  If this is 'Nothing',
                  -- the file system will be empty.
                  , piCommandLineArguments :: [BS.ByteString]
                  -- ^ The command line arguments to pass to the program
                  --
                  -- The caller should ensure that this includes argv[0] (the
                  -- program name)
                  --
                  -- Note that the command line UI can take textual arguments;
                  -- the real arguments here are 'BS.ByteString's because that
                  -- is how they must be represented in the memory model.
                  , piConcreteEnvVars :: [AEnv.ConcreteEnvVar BS.ByteString]
                  -- ^ The environment variables to pass to the program, where
                  -- the values are concrete.
                  , piConcreteEnvVarsFromBytes :: [AEnv.ConcreteEnvVarFromBytes BS.ByteString]
                  -- ^ The environment variables to pass to the program, where
                  -- the values are concrete bytes contained in a file.
                  , piSymbolicEnvVars :: [AEnv.SymbolicEnvVar BS.ByteString]
                  -- ^ The environment variables to pass to the program, where
                  -- the values are symbolic.
                  , piSolver :: AS.Solver
                  -- ^ The solver to use for path satisfiability checking and
                  -- goals
                  , piFloatMode :: AS.FloatMode
                  -- ^ The interpretation of floating point operations in SMT
                  , piProperties :: [APD.Property APD.StateID]
                  -- ^ A property to verify that the program satisfies
                  , piEntryPoint :: AEp.EntryPoint
                  -- ^ Where to begin simulation
                  , piProfileTo :: Maybe FilePath
                  -- ^ Optional directory to write profiler-related files to
                  , piOverrideDir :: Maybe FilePath
                  -- ^ Path to the crucible syntax overrides directory.  If
                  -- this is 'Nothing', then no crucible syntax overrides will
                  -- be registered.
                  , piIterationBound :: Maybe Word64
                  -- ^ If @'Just' n@, bound all loops to at most @n@ iterations.
                  -- If 'Nothing', do not bound the number of loop iterations.
                  , piRecursionBound :: Maybe Word64
                  -- ^ If @'Just' n@, bound the number of recursive calls to at
                  -- most @n@ calls. If 'Nothing', do not bound the number of
                  -- recursive calls.
                  , piSolverInteractionFile :: Maybe FilePath
                  -- ^ Optional location to write solver interactions log to
                  , piSharedObjectDir :: Maybe FilePath
                  -- ^ Optional directory containing shared objects to verify
                  , piLogSymbolicBranches :: Maybe FilePath
                  -- ^ Log symbolic branches to a given file
                  , piLogFunctionCalls :: Maybe FilePath
                  -- ^ Optional location to log function calls to
                  , piCCompiler :: FilePath
                  -- ^ The C compiler to use to preprocess C overrides
                  , piLogObservableEvents :: Maybe FilePath
                  -- ^ Optional file to write observable events occurring after
                  -- weird machine entry to.
                  }

-- | A set of metrics from a verification run
data Metrics =
  Metrics { proofStats :: AVP.ProofStats
         -- ^ Statistics from goal proofs
          , crucibleMetrics :: LCSProf.Metrics Identity
         -- ^ Metrics from the Crucible profiler
          , runtimeSeconds :: DTC.NominalDiffTime
         -- ^ Number of seconds the verifier took to run
          , simulationStats :: AExt.AmbientSimulationStats
         -- ^ Statistics from the simulation step
          , numBytesLoaded :: Int
         -- ^ Total number of bytes loaded (includes shared libraries)
          , blocksVisited :: Int
         -- ^ Total number of blocks visited during symbolic execution
          , uniqueBlocksVisited :: Int }
         -- ^ Number of unique blocks visited during symbolic execution
  deriving (Generic)
instance DA.ToJSON Metrics

instance DA.ToJSON (LCSProf.Metrics Identity)
deriving instance Generic WI.Statistics
instance DA.ToJSON WI.Statistics

-- | Extract the final value from a global variable
--
-- This is slightly tricky, as it needs to handle the various termination and
-- branch abort conditions. Briefly, the resulting value is conditionally valid
-- on all of the branches that did not abort, so there is some mux tree
-- structure to capture that validity.
getFinalGlobal
  :: (WI.IsExprBuilder sym)
  => sym
  -> (WI.SymExpr sym WI.BaseBoolType -> LCS.RegValue sym tp -> LCS.RegValue sym tp -> IO (LCS.RegValue sym tp))
  -> LCS.GlobalVar tp
  -> LCS.ExecResult p sym ext u
  -> IO (LCS.RegValue sym tp)
getFinalGlobal _sym mergeBranches global execResult =
  case execResult of
    LCS.AbortedResult _ res -> handleAbortedResult res
    LCS.FinishedResult _ res ->
      case res of
        LCS.TotalRes gp -> return (getValue global gp)
        LCS.PartialRes _ cond gp abortedRes -> do
          let value = getValue global gp
          onAbort <- handleAbortedResult abortedRes
          mergeBranches cond value onAbort
    LCS.TimeoutResult {} -> X.throwIO AE.ExecutionTimeout
  where
    handleAbortedResult res =
      case res of
        LCS.AbortedExec _ gp -> return (getValue global gp)
        LCS.AbortedBranch _ cond onOK onAbort -> do
          okVal <- handleAbortedResult onOK
          abortVal <- handleAbortedResult onAbort
          mergeBranches cond okVal abortVal
        LCS.AbortedExit {} -> AP.panic AP.Verifier "getFinalGlobal" ["Cannot get global from an AbortedExit"]

    getValue glob gp =
      case LCSG.lookupGlobal glob (gp ^. LCS.gpGlobals) of
        Just value -> value
        Nothing -> AP.panic AP.Verifier "getFinalGlobal" ["Could not find expected global"]

-- | Extract the personality from an 'LCS.ExecResult'.  Throws an exception if
-- the execution timed out.
getPersonality :: LCS.ExecResult p sym ext r -> IO p
getPersonality execResult =
  case execResult of
    LCS.FinishedResult ctx _ -> return $ ctx ^. LCS.cruciblePersonality
    LCS.AbortedResult ctx _ -> return $ ctx ^. LCS.cruciblePersonality
    LCS.TimeoutResult{} -> X.throwIO AE.ExecutionTimeout

-- | The result of observable event trace processing.
data ProcessedObsEventTrace =
    HasWM (Set.Set AO.ObservableEvent)
 -- ^ Some trace(s) contained a weird machine.  The Set contains only events in
 -- that trace (or traces) that contained a weird machine.
  | NoWM (Set.Set AO.ObservableEvent)
 -- ^ No traces contained a weird machine.  The Set contains all events from
 -- all traces.

-- | Reason about the observable event trace to extract only the events that
-- occurred after weird machine entry.  This function writes the event trace
-- out to a JSON file.
processObservableEvents :: forall arch sym
                         . ( WI.IsExprBuilder sym )
                        => sym
                        -> AVS.SymbolicExecutionResult arch sym
                        -- ^ Result from symbolic execution
                        -> FilePath
                        -- ^ File to write event trace to
                        -> IO ()
processObservableEvents sym execResult path = do
  obsEvtTrace <- getFinalGlobal sym
                                (LCSS.muxSymSequence sym)
                                (AVS.serObservableEventGlob execResult)
                                (AVS.serCrucibleExecResult execResult)
  evts <- processTrace obsEvtTrace Set.empty
  DA.encodeFile path (Set.toList (fromHasWM evts))
  where
    -- | If passed a 'HasWM', this function returns the set within.  Otherwise
    -- it returns an emtpy set.
    fromHasWM :: ProcessedObsEventTrace -> Set.Set AO.ObservableEvent
    fromHasWM processedTrace =
      case processedTrace of
        HasWM s -> s
        NoWM _ -> Set.empty

    -- | Recursively process the event trace into a set of observable events
    -- occurring since weird machine entry. Returns a 'ProcessedObsEventTrace'
    -- where 'HasWM' indicates some trace contained a weird machine entry (and
    -- therefore the returned Set is valid), and 'NoWM' indicates that no trace
    -- contained a weird machine.  The function uses the Set built up in the
    -- 'NoWM' case to properly handle recursive traversals over the input
    -- sequence, but other callers of this function should discard this set.
    processTrace :: LCSS.SymSequence sym (WI.SymInteger sym)
                 -- ^ Trace to process
                 -> Set.Set AO.ObservableEvent
                 -- ^ Set of events seen so far
                 -> IO ProcessedObsEventTrace
    processTrace t seen =
      case t of
        LCSS.SymSequenceNil -> do
          -- No WM in this branch
          return $ NoWM seen
        LCSS.SymSequenceCons _ h t' -> do
          let evt = idToEvent h
          case (AO.oeEvent evt) of
            APD.EnterWeirdMachine _ -> do
              -- Done! We were in a WM!  Blank out the parent field as this is
              -- now the parent of the entire trace.
              let evt' = evt { AO.oeParents = [] }
              return $ HasWM $ Set.insert evt' seen
            _ ->
              -- Keep processing
              processTrace t' (Set.insert evt seen)
        LCSS.SymSequenceAppend _ l r -> do
          eSeen' <- processTrace l seen
          case eSeen' of
            HasWM seen' ->
              -- The left side of the append contained the weird machine entry
              -- point.  No need to keep searching
              return $ HasWM $ seen'
            NoWM seen' ->
              -- The left side of the append did not contain the weird machine
              -- entry point.  Continue searching down the right hand side
              processTrace r seen'
        LCSS.SymSequenceMerge _ _ l r -> do
          -- Process both branches
          elSeen' <- processTrace l seen
          erSeen' <- processTrace r seen
          case (elSeen', erSeen') of
            (HasWM lSeen', HasWM rSeen') ->
              -- Both sides contained weird machines
              return $ HasWM $ Set.union lSeen' rSeen'
            (HasWM lSeen', NoWM _) ->
              -- Only the left branch contained a weird machine
              return $ HasWM lSeen'
            (NoWM _, HasWM rSeen') ->
              -- Only the right branch contained a weird machine
              return $ HasWM rSeen'
            (NoWM lSeen', NoWM rSeen') ->
              -- Neither side contained a weird machine
              return $ NoWM $ Set.union lSeen' rSeen'

    -- | Extract the event corresponding to an ID.
    idToEvent :: WI.SymInteger sym -> AO.ObservableEvent
    idToEvent symEvtId =
      case WI.asInteger symEvtId of
        Just evtId ->
          let mEvt = Map.lookup (fromInteger evtId)
                                (AVS.serObservableEventMap execResult) in
          case mEvt of
            Just evt -> evt
            Nothing -> AP.panic AP.Verifier
                                "processObservableEvents"
                                ["No event corresponds to id " ++ (show evtId)]
        Nothing ->
          -- This shouldn't be possible because we only insert concrete
          -- integers into the sequence.
          AP.panic AP.Verifier
                   "processObservableEvents"
                   ["Encountered symbolic event ID"]

-- | Extract the trace and assert that the last state is an accept state (along all branches)
--
-- The verification condition is that the final state is at least one of the
-- accept states and definitely not one of the non-accept states.
assertPropertySatisfied
  :: ( LCB.IsSymBackend sym bak
     , LCS.RegValue sym tp ~ LCSS.SymSequence sym (WI.SymExpr sym WI.BaseIntegerType)
     )
  => LJ.LogAction IO AD.Diagnostic
  -> bak
  -> LCS.ExecResult p sym ext u
  -> (APD.Property APD.StateID, LCS.GlobalVar tp)
  -> IO ()
assertPropertySatisfied logAction bak execResult (prop, globalTraceVar) = do
  let sym = LCB.backendGetSym bak
  LJ.writeLog logAction (AD.AssertingGoalsForProperty (APD.propertyName prop) (APD.propertyDesscription prop))
  let merge = LCSS.muxSymSequence sym
  evtTrace <- getFinalGlobal sym merge globalTraceVar execResult
  phd <- LCSS.headSymSequence sym (WI.intIte sym) evtTrace
  case phd of
    WP.Err _ -> X.throwIO (AE.MalformedEventTrace (APD.propertyName prop))
    WP.NoErr partial -> do
      case APD.propertyFinalStates prop of
        APD.AlwaysOneOf acceptIds -> do
          -- print (WI.printSymExpr (partial ^. WP.partialValue))
          -- let acceptIds = fmap APD.stateID (APD.acceptStates prop)
          let testAccept val acceptId = do
                acceptInt <- WI.intLit sym (APD.stateID acceptId)
                eq <- WI.intEq sym acceptInt (partial ^. WP.partialValue)
                WI.orPred sym eq val
          allAccept <- F.foldlM testAccept (WI.falsePred sym) acceptIds
          LCB.assert bak allAccept (LCSS.AssertFailureSimError ("Property not satisfied " ++ show (APD.propertyName prop)) "")
        APD.PossiblyOneOfOr conditionalAccepts -> do
          let testConditionalAccept val (acceptId, others) = do
                -- We want it to be the case that either the final state is
                -- acceptId *or* it is one of the other acceptable states:
                --
                -- (acceptId == finalState) \/ ((acceptId != finalState) => (finalState == o_1 \/ finalState == o_n))
                acceptInt <- WI.intLit sym (APD.stateID acceptId)
                eqAccept <- WI.intEq sym acceptInt (partial ^. WP.partialValue)
                neqAccept <- WI.notPred sym eqAccept
                let checkAlternative acc ostate = do
                      otherLit <- WI.intLit sym (APD.stateID ostate)
                      eqOther <- WI.intEq sym otherLit (partial ^. WP.partialValue)
                      WI.orPred sym eqOther acc
                isAnyAllowedOther <- F.foldlM checkAlternative (WI.falsePred sym) others
                otherIfNotAccept <- WI.impliesPred sym neqAccept isAnyAllowedOther
                WI.orPred sym val =<< WI.orPred sym eqAccept otherIfNotAccept
          valid <- F.foldlM testConditionalAccept (WI.falsePred sym) conditionalAccepts
          LCB.assert bak valid (LCSS.AssertFailureSimError ("Property not satisfied " ++ show (APD.propertyName prop)) "")


setupProfiling
  :: FilePath
  -> IO (LCS.GenericExecutionFeature sym, CCA.Async ())
setupProfiling dir = do
  F.for_ APE.profilerDataFiles $ \(fp, contents) ->
    createDirectoriesAndWriteFile (dir FP.</> fp) contents
  tbl <- LCSProf.newProfilingTable
  let flt = LCSProf.profilingEventFilter
  let reportPath = dir FP.</> "report_data.js"
  let doLog = do
        LCSProf.writeProfileReport reportPath "ambient-verifier-profile" "ambient-verifier" tbl
        CC.threadDelay 1000000
        doLog
  logger <- CCA.async doLog
  opt <- LCSProf.profilingFeature tbl flt Nothing -- (Just opts)
  return (opt, logger)

-- | Like 'BS.writeFile', but also create parent directories if they are
-- missing.
createDirectoriesAndWriteFile :: FilePath -> BS.ByteString -> IO ()
createDirectoriesAndWriteFile path bs = do
  let dir = FP.takeDirectory path
  Dir.createDirectoryIfMissing True dir
  BS.writeFile path bs

-- | Build an LLVM annotation tracker to record instances of bad behavior
-- checks.  Bad behavior encompasses both undefined behavior, and memory
-- errors.  This function returns a function to set '?recordLLVMAnnotation' to,
-- as well as a reference to the record of bad behaviors that will be built up.
buildRecordLLVMAnnotation
  :: LCB.IsSymInterface sym
  => IO ( LCLMC.CallStack -> LCLMP.BoolAnn sym -> LCLE.BadBehavior sym -> IO ()
        , IORef (LCLM.LLVMAnnMap sym) )
buildRecordLLVMAnnotation = do
  badBehavior <- liftIO $ newIORef Map.empty
  let recordFn = \cs ann behavior ->
        modifyIORef' badBehavior (Map.insert ann (cs, behavior))
  return (recordFn , badBehavior)

-- | Verify that the given 'ProgramInstance' terminates (with the given input)
-- without raising an error
verify
  :: ( MonadIO m
     , CMC.MonadMask m
     , CMC.MonadThrow m
     , HasCallStack)
  => LJ.LogAction IO AD.Diagnostic
  -- ^ A logger to report diagnostic information to the caller
  -> ProgramInstance
  -- ^ A description of the program (and its configuration) to verify
  -> AT.Timeout
  -- ^ The solver timeout for each goal
  -> m Metrics
verify logAction pinst timeoutDuration = do
  t0 <- liftIO $ DTC.getCurrentTime
  hdlAlloc <- liftIO LCF.newHandleAllocator
  Some ng <- liftIO PN.newIONonceGenerator
  AS.withOnlineSolver (piSolver pinst) (piFloatMode pinst) ng $ \bak -> do
    let sym = LCB.backendGetSym bak
    liftIO $ case (piSolverInteractionFile pinst) of
      Just path -> do
        let config = WI.getConfiguration sym
        interactionFileSetter <- WConf.getOptionSetting LCBO.solverInteractionFile
                                                        config
        void $ WConf.setOption interactionFileSetter
                               (WC.ConcreteString (WI.UnicodeLiteral (DT.pack path)))
      Nothing -> return ()

    -- Track instances of bad behavior (undefined behavior and memory errors)
    (recordFn, badBehavior) <- liftIO $ buildRecordLLVMAnnotation
    let ?recordLLVMAnnotation = recordFn

    -- Load up the binary, which existentially introduces the architecture of the
    -- binary in the context of the continuation
    AL.withBinary (piPath pinst) (piBinary pinst) (piSharedObjectDir pinst) hdlAlloc sym $ \archInfo archVals syscallABI functionABI parserHooks buildGlobals numBytes binConf -> DMA.withArchConstraints archInfo $ do
      entryPointAddr <- AEp.resolveEntryPointAddrOff binConf $ piEntryPoint pinst

      profFeature <- liftIO $ mapM setupProfiling (piProfileTo pinst)
      iterationBoundFeature <-
        Trav.for (piIterationBound pinst) $ \i ->
          liftIO $ LCSBE.boundedExecFeature (\_ -> return (Just i)) True
      recursionBoundFeature <-
        Trav.for (piRecursionBound pinst) $ \i ->
          liftIO $ LCSBR.boundedRecursionFeature (\_ -> return (Just i)) True
      -- We set up path satisfiability checking here so that we do not have to
      -- require the online backend constraints in the body of our symbolic
      -- execution code
      psf <- liftIO $ LCSP.pathSatisfiabilityFeature sym (LCBO.considerSatisfiability bak)

      -- Set up a profiling instance for collection of stats within a 'Metrics'
      -- instance.
      profTab <- liftIO $ LCSProf.newProfilingTable
      let profFilt = LCSProf.profilingEventFilter {
          LCSProf.recordProfiling = True
        , LCSProf.recordCoverage = True
        }
      metricsProfFeat <-
        liftIO $ LCSProf.profilingFeature profTab profFilt Nothing

      let execFeatures = psf
                       : metricsProfFeat
                       : catMaybes [ fmap fst profFeature
                                   , iterationBoundFeature
                                   , recursionBoundFeature
                                   ]
      let seConf = AVS.SymbolicExecutionConfig
                     { AVS.secProperties = piProperties pinst
                     , AVS.secWMMCallback = \initialMem abi props oec ->
                         AVWme.wmExecutor logAction bak initialMem binConf abi
                                          hdlAlloc archInfo props archVals
                                          (piLogFunctionCalls pinst) oec
                                          execFeatures
                     , AVS.secSolver = piSolver pinst
                     , AVS.secLogBranches = isJust $ piLogSymbolicBranches pinst
                     }
      let ?memOpts = LCLM.defaultMemOptions
      csOverrides <-
        case piOverrideDir pinst of
          Just dir -> do
            liftIO $ AFE.loadCrucibleSyntaxOverrides dir (piCCompiler pinst) ng hdlAlloc parserHooks
          Nothing -> return AFE.emptyCrucibleSyntaxOverrides
      let fnConf = AVS.FunctionConfig {
          AVS.fcBuildSyscallABI = syscallABI
        , AVS.fcBuildFunctionABI = functionABI
        , AVS.fcCrucibleSyntaxOverrides = csOverrides
        }
      envVarMap <- liftIO $ AEnv.mkEnvVarMap
                              bak
                              (piConcreteEnvVars pinst)
                              (piConcreteEnvVarsFromBytes pinst)
                              (piSymbolicEnvVars pinst)

      ambientExecResult <- AVS.symbolicallyExecute logAction bak hdlAlloc archInfo archVals seConf execFeatures entryPointAddr buildGlobals (piFsRoot pinst) (piLogFunctionCalls pinst) binConf fnConf (piCommandLineArguments pinst) envVarMap
      let crucibleExecResult = AVS.serCrucibleExecResult ambientExecResult
      badBehavior' <- liftIO $ readIORef badBehavior

      liftIO $ mapM_ (assertPropertySatisfied logAction bak crucibleExecResult) (AEt.properties (AVW.wmProperties (AVS.serWMConfig ambientExecResult)))

      -- Prove all of the side conditions asserted during symbolic execution;
      -- these are captured in the symbolic backend (sym)
      --
      -- NOTE: In the longer term, we will want to separate proving from this
      -- symbolic execution pass.
      --
      -- NOTE: We currently use the same solver for goal solving as we do for
      -- symbolic execution/path sat checking. This is not required, and we
      -- could easily support allowing the user to choose two different solvers.
      metricProofStats <- AVP.proveObligations logAction bak (AS.offlineSolver (piSolver pinst)) timeoutDuration badBehavior'

      liftIO $
        F.traverse_ (\path -> processObservableEvents sym
                                                      ambientExecResult
                                                      path)
                    (piLogObservableEvents pinst)

      crucMetrics <- liftIO $ LCSProf.readMetrics profTab
      _ <- liftIO $ mapM CCA.cancel (fmap snd profFeature)

      -- Extract block metrics from Crucible profiler
      profEvents <- liftIO $ readIORef (LCSProf.callGraphEvents profTab)
      let blockEvents = [ LCSProf.cgEvent_blocks e
                        | e <- F.toList profEvents
                        , LCSProf.cgEvent_type e == LCSProf.BLOCK ]
      let uniqueBlockEvents = Set.fromList blockEvents

      aSymSt <- liftIO $ getPersonality crucibleExecResult

      t1 <- liftIO $ DTC.getCurrentTime
      return Metrics
        { proofStats = metricProofStats
        , crucibleMetrics = crucMetrics
        , runtimeSeconds = t1 `DTC.diffUTCTime` t0
        , simulationStats = aSymSt ^. AExt.simulationStats
        , numBytesLoaded = numBytes
        , blocksVisited = length blockEvents
        , uniqueBlocksVisited = Set.size uniqueBlockEvents
        }


{- Note [Entry Point]

Right now, we are starting verification from ~main~ instead of ~_start~ (or
whatever the ELF entrypoint function happens to be named). Macaw
can have trouble analyzing from ~_start~, especially in stripped binaries,
because the startup sequence passes function pointers indirectly to kick off
main.

This can be fixed up later by lazily re-running discovery as we identify new
entry points (i.e., by demand as they are jumped to through function pointers).
See Note [Incremental code discovery] in A.Extensions.

The other complexity is that there is substantial state that must be reasonably
concrete for symbolic execution from ~_start~ to terminate. We will eventually
fill all of that in.

-}
