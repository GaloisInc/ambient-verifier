{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Control.Exception as X
import qualified Data.ByteString as BS
import qualified Data.Yaml as DY
import qualified Data.Text.Encoding as TE
import qualified Lumberjack as LJ
import qualified Options.Applicative as OA
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PPT
import qualified System.IO as IO

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Exception as AE
import qualified Ambient.Override.List as AOL
import qualified Ambient.OverrideTester as AO
import qualified Ambient.Property.Definition as APD
import qualified Ambient.Verifier as AV

import qualified Options as O

-- | A simple logger that just sends diagnostics to a channel; an asynchronous
-- thread will process these messages (different UIs can process them as needed)
logAction :: CC.Chan (Maybe AD.Diagnostic) -> LJ.LogAction IO AD.Diagnostic
logAction c = LJ.LogAction (CC.writeChan c . Just)

-- | This log consumer prints log messages to the given handle
printLogs ::
  Maybe IO.Handle ->
  -- ^ If @'Just' hdl@, write function CFG–related logs to @hdl@.
  -- If 'Nothing', do not write function CFG–related logs at all.
  IO.Handle ->
  -- ^ The file handle to write all logs, except for the special case in the
  --   first argument.
  CC.Chan (Maybe AD.Diagnostic) ->
  IO ()
printLogs mbFunctionCFGsHdl hdl chan = go
  where
    go = do
      mdiag <- CC.readChan chan
      case mdiag of
        Nothing -> return ()
        Just d -> do
          let ppd = PP.pretty d
          case d of
            AD.DiscoveryEvent{} ->
              case mbFunctionCFGsHdl of
                Nothing -> pure ()
                Just functionCFGsHdl
                  -> PPT.hPutDoc functionCFGsHdl ppd
            _ -> PPT.hPutDoc hdl ppd
          go

loadProperty :: FilePath -> IO (APD.Property APD.StateID)
loadProperty fp = do
  bytes <- BS.readFile fp
  val <- DY.decodeThrow bytes
  APD.parseProperty val

-- | Like 'IO.withFile', but lifted to work over 'Maybe'.
withMaybeFile :: Maybe FilePath -> IO.IOMode -> (Maybe IO.Handle -> IO r) -> IO r
withMaybeFile mbFP mode action =
  case mbFP of
    Just fp -> IO.withFile fp mode (action . Just)
    Nothing -> action Nothing

-- | This is the real verification driver that takes the parsed out command line
-- arguments and sets up the problem instance for the library core
verify :: O.VerifyOptions -> IO ()
verify o = withMaybeFile (O.functionCFGsFile o) IO.WriteMode $ \mbFunCFGsHdl -> do
  binary <- BS.readFile (O.binaryPath o)
  -- See Note [Argument Encoding]
  let args = fmap TE.encodeUtf8 (O.commandLineArguments o)

  props <- mapM loadProperty (O.stateCharts o)

  let pinst = AV.ProgramInstance { AV.piPath = O.binaryPath o
                                 , AV.piBinary = binary
                                 , AV.piFsRoot = O.fsRoot o
                                 , AV.piCommandLineArguments = args
                                 , AV.piSolver = O.solver o
                                 , AV.piFloatMode = O.floatMode o
                                 , AV.piProperties = props
                                 , AV.piProfileTo = O.profileTo o
                                 , AV.piOverrideDir = O.overrideDir o
                                 , AV.piSolverInteractionFile = O.solverInteractionFile o
                                 }

  chan <- CC.newChan
  logger <- CCA.async (printLogs mbFunCFGsHdl IO.stdout chan)

  AV.verify (logAction chan) pinst (O.timeoutDuration o)

  -- Tear down the logger by sending the token that causes it to exit cleanly
  CC.writeChan chan Nothing
  CCA.wait logger

  return ()

-- | This is the test runner for user function overrides that takes parsed
-- command line arguments and sets up the test instance
testOverrides :: O.TestOverridesOptions -> IO ()
testOverrides o = do
  let tinst =  AO.TestInstance { AO.tiSolver = O.testSolver o
                               , AO.tiFloatMode = O.testFloatMode o
                               , AO.tiOverrideDir = O.testOverrideDir o
                               , AO.tiAbi = O.testAbi o
                               }
  chan <- CC.newChan
  logger <- CCA.async (printLogs Nothing IO.stdout chan)

  AO.testOverrides (logAction chan) tinst (O.testTimeoutDuration o)

  -- Tear down the logger by sending the token that causes it to exit cleanly
  CC.writeChan chan Nothing
  CCA.wait logger

  return ()

-- | Like 'verify', except that this stops short of actually verifying the
-- binary. Instead, it prints all of the overrides that are registered for the
-- particular binary and exits.
listOverrides :: O.VerifyOptions -> IO ()
listOverrides o = withMaybeFile (O.functionCFGsFile o) IO.WriteMode $ \mbFunCFGsHdl -> do
  binary <- BS.readFile (O.binaryPath o)
  -- See Note [Argument Encoding]
  let args = fmap TE.encodeUtf8 (O.commandLineArguments o)

  props <- mapM loadProperty (O.stateCharts o)

  let pinst = AV.ProgramInstance { AV.piPath = O.binaryPath o
                                 , AV.piBinary = binary
                                 , AV.piFsRoot = O.fsRoot o
                                 , AV.piCommandLineArguments = args
                                 , AV.piSolver = O.solver o
                                 , AV.piFloatMode = O.floatMode o
                                 , AV.piProperties = props
                                 , AV.piProfileTo = O.profileTo o
                                 , AV.piOverrideDir = O.overrideDir o
                                 , AV.piSolverInteractionFile = O.solverInteractionFile o
                                 }

  chan <- CC.newChan
  logger <- CCA.async (printLogs mbFunCFGsHdl IO.stdout chan)

  AOL.listOverrides (logAction chan) pinst

  -- Tear down the logger by sending the token that causes it to exit cleanly
  CC.writeChan chan Nothing
  CCA.wait logger

main :: IO ()
main =
  X.catch
    (do
      command <- OA.execParser opts
      case command of
        O.Verify verifyOpts -> verify verifyOpts
        O.ListOverrides listOverridesOpts -> listOverrides listOverridesOpts
        O.TestOverrides testOverridesOpts -> testOverrides testOverridesOpts
    )
    (\(e :: AE.AmbientException) -> IO.hPutStrLn IO.stderr (show (PP.pretty e)))
  where
    opts = OA.info (O.parser OA.<**> OA.helper)
             ( OA.fullDesc
               <> OA.header "A verifier for programs containing weird machines"
             )

{- Note [Argument Encoding]

This current method of specifying command line arguments supports accepts
textual arguments on the command line.  If we need to support binary arguments, we will need to add
an alternative command line interface for providing them in a file.

Note that we are unconditionally encoding arguments from Text to UTF8. This
works for Linux and MacOS, but will not work for Windows, which will expect
UTF16LE (or perhaps UCS-2).

-}
