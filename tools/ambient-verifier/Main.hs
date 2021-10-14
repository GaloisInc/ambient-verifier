module Main ( main ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Data.ByteString as BS
import qualified Data.Yaml as DY
import qualified Data.Text.Encoding as TE
import qualified Lumberjack as LJ
import qualified Options.Applicative as OA
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PPT
import qualified System.IO as IO

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Property.Definition as APD
import qualified Ambient.Verifier as AV

import qualified Options as O

-- | A simple logger that just sends diagnostics to a channel; an asynchronous
-- thread will process these messages (different UIs can process them as needed)
logAction :: CC.Chan (Maybe AD.Diagnostic) -> LJ.LogAction IO AD.Diagnostic
logAction c = LJ.LogAction (CC.writeChan c . Just)

-- | This log consumer prints log messages to the given handle
printLogs :: IO.Handle -> CC.Chan (Maybe AD.Diagnostic) -> IO ()
printLogs hdl chan = go
  where
    go = do
      mdiag <- CC.readChan chan
      case mdiag of
        Nothing -> return ()
        Just d -> do
          PPT.hPutDoc hdl (PP.pretty d)
          go

loadProperty :: FilePath -> IO (APD.Property APD.StateID)
loadProperty fp = do
  bytes <- BS.readFile fp
  val <- DY.decodeThrow bytes
  APD.parseProperty val

-- | This is the real verification driver that takes the parsed out command line
-- arguments and sets up the problem instance for the library core
verify :: O.Options -> IO ()
verify o = do
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
                                 }

  chan <- CC.newChan
  logger <- CCA.async (printLogs IO.stdout chan)

  AV.verify (logAction chan) pinst (O.timeoutDuration o)

  -- Tear down the logger by sending the token that causes it to exit cleanly
  --
  -- Note that the log printer will
  CC.writeChan chan Nothing
  CCA.wait logger

  return ()

main :: IO ()
main = verify =<< OA.execParser opts
  where
    opts = OA.info (O.parser OA.<**> OA.helper)
             ( OA.fullDesc
               <> OA.progDesc "Verify that the given binary with inputs terminates cleanly"
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
