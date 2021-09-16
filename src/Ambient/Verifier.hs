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

import           Control.Lens ( (^.) )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Word ( Word64 )
import           GHC.Stack ( HasCallStack )
import qualified Lumberjack as LJ

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.PathSatisfiability as LCSP

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Discovery as ADi
import qualified Ambient.Exception as AE
import qualified Ambient.Lift as ALi
import qualified Ambient.Loader as AL
import qualified Ambient.Solver as AS
import qualified Ambient.Timeout as AT
import qualified Ambient.Verifier.Prove as AVP
import qualified Ambient.Verifier.SymbolicExecution as AVS
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
                  , piStdin :: Maybe BS.ByteString
                  -- ^ The contents to be passed to the program via standard
                  -- input, which can be empty
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
                  , piWeirdMachineEntries :: [Word64]
                  -- ^ Expected entry points to Weird Machines; if execution
                  -- reaches here, a Weird Machine needs to be executed via the
                  -- 'AVW.WMMCallback'
                  , piWeirdMachineCallback :: AVW.WMMCallback
                  -- ^ The action to run when a Weird Machine is entered; this
                  -- could launch a new symbolic execution process for the Weird
                  -- Machine
                  }

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
  let symbolNamesToAddrs = Map.fromList [ (name, addr)
                                        | (addr, name) <- Map.toList (DMD.symbolNames discoveryState)
                                        ]
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
  -- Load up the binary, which existentially introduces the architecture of the
  -- binary in the context of the continuation
  AL.withBinary (piPath pinst) (piBinary pinst) hdlAlloc $ \archInfo archVals syscallABI buildGlobals loadedBinary -> DMA.withArchConstraints archInfo $ do
    discoveryState <- ADi.discoverFunctions logAction archInfo loadedBinary
    -- See Note [Entry Point] for more details
    (entryAddr, Some discoveredEntry) <- getNamedFunction discoveryState "main"
    (LCCC.SomeCFG cfg0) <- ALi.liftDiscoveredFunction hdlAlloc (piPath pinst) (DMS.archFunctions archVals) discoveredEntry
    Some ng <- liftIO PN.newIONonceGenerator
    AS.withOnlineSolver (piSolver pinst) (piFloatMode pinst) ng $ \sym -> do
      (handles, bindings) <- buildBindings
          (Map.toList (discoveryState ^. DMD.funInfo))
          hdlAlloc
          pinst
          archVals
          entryAddr
          cfg0
      -- We set up path satisfiability checking here so that we do not have to
      -- require the online backend constraints in the body of our symbolic
      -- execution code
      psf <- liftIO $ LCSP.pathSatisfiabilityFeature sym (LCBO.considerSatisfiability sym)
      let execFeatures = [psf]
      let seConf = AVS.SymbolicExecutionConfig { AVS.secWMEntries = piWeirdMachineEntries pinst
                                               , AVS.secWMMCallback = piWeirdMachineCallback pinst
                                               , AVS.secSolver = piSolver pinst
                                               }
      let ?memOpts = LCLM.defaultMemOptions
      AVS.symbolicallyExecute logAction sym hdlAlloc archInfo archVals seConf loadedBinary execFeatures cfg0 (DMD.memory discoveryState) (Map.fromList handles) bindings syscallABI buildGlobals

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
