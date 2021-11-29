{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
-- | The main entry point of the AMBIENT binary verifier
module Ambient.Verifier (
    ProgramInstance(..)
  , verify
  ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Control.Exception as X
import           Control.Lens ( (^.) )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Maybe ( maybeToList )
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import           GHC.Stack ( HasCallStack )
import qualified Lumberjack as LJ

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Simulator.PathSatisfiability as LCSP
import qualified Lang.Crucible.Simulator.Profiling as LCSProf
import qualified Lang.Crucible.Simulator.SimError as LCSS
import qualified Lang.Crucible.Simulator.SymSequence as LCSS
import qualified What4.Interface as WI
import qualified What4.Partial as WP

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Discovery as ADi
import qualified Ambient.EventTrace as AEt
import qualified Ambient.Exception as AE
import qualified Ambient.FunctionOverride.Extension as AFE
import qualified Ambient.Lift as ALi
import qualified Ambient.Loader as AL
import qualified Ambient.Panic as AP
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
                  , piSolver :: AS.Solver
                  -- ^ The solver to use for path satisfiability checking and
                  -- goals
                  , piFloatMode :: AS.FloatMode
                  -- ^ The interpretation of floating point operations in SMT
                  , piProperties :: [APD.Property APD.StateID]
                  -- ^ A property to verify that the program satisfies
                  , piProfileTo :: Maybe FilePath
                  -- ^ The path of a file to profile to
                  , piOverrideDir :: Maybe FilePath
                  -- ^ Path to the crucible syntax overrides directory.  If
                  -- this is 'Nothing', then no crucible syntax overrides will
                  -- be registered.
                  }

-- | Retrieve a mapping from symbol names to addresses from code discovery
-- information.
getSymbolNameToAddrMapping
  :: DMD.DiscoveryState arch
  -> Map.Map BSC.ByteString
             (DMM.MemSegmentOff (DMC.RegAddrWidth (DMC.ArchReg arch)))
getSymbolNameToAddrMapping discoveryState =
  Map.fromList [ (name, addr)
               | (addr, name) <- Map.toList (DMD.symbolNames discoveryState)
               ]

-- | Retrieve the named function (in its 'DMD.DiscoveryFunInfo' form) from the code
-- discovery information.  Returns a pair containing the address of the named
-- function, as well as the named function.
--
-- If the symbol is not present in the binary, or if discovery was unable to
-- find it, this function will throw exceptions.
getNamedFunction
  :: ( CMC.MonadThrow m
     , DMM.MemWidth (DMC.ArchAddrWidth arch)
     , w ~ DMC.RegAddrWidth (DMC.ArchReg arch)
     )
  => DMD.DiscoveryState arch
  -- ^ A computed discovery state
  -> String
  -- ^ The name of the function to retrieve
  -> m (DMM.MemSegmentOff w, (Some (DMD.DiscoveryFunInfo arch)))
getNamedFunction discoveryState fname = do
  let entryPointName = BSC.pack fname
  let symbolNamesToAddrs = getSymbolNameToAddrMapping discoveryState
  case Map.lookup entryPointName symbolNamesToAddrs of
    Nothing -> CMC.throwM (AE.MissingExpectedSymbol entryPointName)
    Just entryAddr
      | Just dfi <- Map.lookup entryAddr (discoveryState ^. DMD.funInfo) -> return (entryAddr, dfi)
      | otherwise -> CMC.throwM (AE.MissingExpectedFunction (Just entryPointName) entryAddr)

-- | Build function bindings from a list of discovered function.  Returns a
-- pair containing:
--  * A list of pairs, where each pair consists of:
--    * A function address 'addr'
--    * A function handle for 'addr'
--  * Function handle map in the 'LCF.FnHandleMap' form
buildBindings
  :: (MonadIO m,
      DMM.MemWidth (DMC.RegAddrWidth (DMC.ArchReg arch)))
  => [(DMM.MemSegmentOff w, Some (DMD.DiscoveryFunInfo arch))]
  -- ^ List containing pairs of addresses and corresponding discovered
  -- functions
  -> LCF.HandleAllocator
  -> ProgramInstance
  -> DMS.GenArchVals mem arch
  -> DMM.MemSegmentOff w
  -- ^ Entry point address
  -> LCCC.CFG (DMS.MacawExt arch)
              blocks
              (LCCC.EmptyCtx LCCC.::> DMS.ArchRegStruct arch)
              (DMS.ArchRegStruct arch)
  -- ^ CFG for entry point
  -> m ([(DMM.MemSegmentOff w,
          LCF.FnHandle
            (LCCC.EmptyCtx
             LCCC.::> LCCC.StructType
                        (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
            (LCCC.StructType
               (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))))],
        LCF.FnHandleMap (LCS.FnState (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)))
buildBindings fns hdlAlloc pinst archVals entryAddr cfg0 = do
  case fns of
    [] -> return ([], LCF.emptyHandleMap)
    (addr, fn):fns' -> do
      (handles, bindings) <- buildBindings fns' hdlAlloc pinst archVals entryAddr cfg0
      (handle, binding) <- buildBinding fn bindings addr
      return ((addr, handle) : handles, binding)
  where
    -- Given a Crucible CFG 'cfg' and a function handle map, returns a function
    -- handle for 'cfg' and an updated handle map.
    buildBindingFromCfg cfg handleMap = do
      let handle = LCCC.cfgHandle cfg
      let fnBindings = LCF.insertHandleMap handle (LCS.UseCFG cfg (LCAP.postdomInfo cfg)) handleMap
      (handle, fnBindings)
    -- Given a discovered function 'fn', a function handle map, and the address
    -- of 'fn', returns a function handle for 'fn' and an updated handle map.
    buildBinding (Some fn) handleMap addr = do
      if addr == entryAddr
      then return $ buildBindingFromCfg cfg0 handleMap
      else do
        LCCC.SomeCFG cfg <- ALi.liftDiscoveredFunction hdlAlloc (piPath pinst) (DMS.archFunctions archVals) fn
        return $ buildBindingFromCfg cfg handleMap

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

-- | Extract the trace and assert that the last state is an accept state (along all branches)
--
-- The verification condition is that the final state is at least one of the
-- accept states and definitely not one of the non-accept states.
assertPropertySatisfied
  :: ( LCB.IsSymInterface sym
     , LCS.RegValue sym tp ~ LCSS.SymSequence sym (WI.SymExpr sym WI.BaseIntegerType)
     )
  => LJ.LogAction IO AD.Diagnostic
  -> sym
  -> LCS.ExecResult p sym ext u
  -> (APD.Property APD.StateID, LCS.GlobalVar tp)
  -> IO ()
assertPropertySatisfied logAction sym execResult (prop, globalTraceVar) = do
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
          LCB.assert sym allAccept (LCSS.AssertFailureSimError ("Property not satisfied " ++ show (APD.propertyName prop)) "")
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
          LCB.assert sym valid (LCSS.AssertFailureSimError ("Property not satisfied " ++ show (APD.propertyName prop)) "")


setupProfiling
  :: FilePath
  -> IO (LCS.GenericExecutionFeature sym, CCA.Async ())
setupProfiling path = do
  tbl <- LCSProf.newProfilingTable
  let flt = LCSProf.profilingEventFilter
  let doLog = do
        LCSProf.writeProfileReport path "ambient-verifier-profile" "ambient-verifier" tbl
        CC.threadDelay 1000000
        doLog
  logger <- CCA.async doLog
  opt <- LCSProf.profilingFeature tbl flt Nothing -- (Just opts)
  return (opt, logger)

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
  -> m ()
verify logAction pinst timeoutDuration = do
  hdlAlloc <- liftIO LCF.newHandleAllocator
  Some ng <- liftIO PN.newIONonceGenerator
  AS.withOnlineSolver (piSolver pinst) (piFloatMode pinst) ng $ \sym -> do
    -- Load up the binary, which existentially introduces the architecture of the
    -- binary in the context of the continuation
    AL.withBinary (piPath pinst) (piBinary pinst) hdlAlloc sym $ \archInfo archVals syscallABI functionABI parserHooks buildGlobals loadedBinary -> DMA.withArchConstraints archInfo $ do
      discoveryState <- ADi.discoverFunctions logAction archInfo loadedBinary
      -- See Note [Entry Point] for more details
      (entryAddr, Some discoveredEntry) <- getNamedFunction discoveryState "main"
      (LCCC.SomeCFG cfg0) <- ALi.liftDiscoveredFunction hdlAlloc (piPath pinst) (DMS.archFunctions archVals) discoveredEntry
      (handles, bindings) <- buildBindings
          (Map.toList (discoveryState ^. DMD.funInfo))
          hdlAlloc
          pinst
          archVals
          entryAddr
          cfg0

      profFeature <- liftIO $ mapM setupProfiling (piProfileTo pinst)

      -- We set up path satisfiability checking here so that we do not have to
      -- require the online backend constraints in the body of our symbolic
      -- execution code
      psf <- liftIO $ LCSP.pathSatisfiabilityFeature sym (LCBO.considerSatisfiability sym)
      let execFeatures = maybeToList (fmap fst profFeature) ++ [psf]
      let seConf = AVS.SymbolicExecutionConfig { AVS.secProperties = piProperties pinst
                                               , AVS.secWMMCallback = AVWme.wmExecutor archInfo loadedBinary hdlAlloc archVals execFeatures sym
                                               , AVS.secSolver = piSolver pinst
                                               }
      let ?memOpts = LCLM.defaultMemOptions
      functionOvs <- case piOverrideDir pinst of
        Just dir -> liftIO $ AFE.loadCrucibleSyntaxOverrides dir ng hdlAlloc parserHooks
        Nothing -> return []
      (_, execResult, wmConfig) <- AVS.symbolicallyExecute logAction sym hdlAlloc archInfo archVals seConf loadedBinary execFeatures cfg0 (DMD.memory discoveryState) (Map.fromList handles) bindings syscallABI functionABI buildGlobals (piFsRoot pinst) functionOvs

      liftIO $ mapM_ (assertPropertySatisfied logAction sym execResult) (AEt.properties (AVW.wmProperties wmConfig))

      -- Prove all of the side conditions asserted during symbolic execution;
      -- these are captured in the symbolic backend (sym)
      --
      -- NOTE: In the longer term, we will want to separate proving from this
      -- symbolic execution pass.
      --
      -- NOTE: We currently use the same solver for goal solving as we do for
      -- symbolic execution/path sat checking. This is not required, and we
      -- could easily support allowing the user to choose two different solvers.
      AVP.proveObligations logAction sym (AS.offlineSolver (piSolver pinst)) timeoutDuration
      _ <- liftIO $ mapM CCA.cancel (fmap snd profFeature)
      return ()


{- Note [Entry Point]

Right now, we are starting verification from ~main~ instead of ~_start~. Macaw
can have trouble analyzing from ~_start~, especially in stripped binaries,
because the startup sequence passes function pointers indirectly to kick off
main.

This can be fixed up later by lazily re-running discovery as we identify new
entry points (i.e., by demand as they are jumped to through function pointers).

The other complexity is that there is substantial state that must be reasonably
concrete for symbolic execution from ~_start~ to terminate. We will eventually
fill all of that in.

-}
