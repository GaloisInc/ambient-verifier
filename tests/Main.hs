{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
module Main ( main ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Data.ByteString as BS
import qualified Data.Yaml as DY
import           GHC.Generics ( Generic )
import qualified Lumberjack as LJ
import qualified System.FilePath as SF
import qualified System.FilePath.Glob as SFG
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Solver as AS
import qualified Ambient.Verifier as AV

data ExpectedGoals =
  ExpectedGoals { successful :: Int
                , failed :: Int
                }
  deriving (Eq, Ord, Read, Show, Generic)

instance DY.FromJSON ExpectedGoals

emptyExpectedGoals :: ExpectedGoals
emptyExpectedGoals = ExpectedGoals { successful = 0
                                   , failed = 0
                                   }

-- | A simple logger that just sends diagnostics to a channel; an asynchronous
-- thread will analyze the successfully and unsuccessfully solved goals
logAction :: CC.Chan (Maybe AD.Diagnostic) -> LJ.LogAction IO AD.Diagnostic
logAction c = LJ.LogAction (CC.writeChan c . Just)

-- | Analyze the generated event stream and count the number of successfully
-- verified and unsuccessfully not verified goals.  These counts are collected
-- into the same structure type as used as the expected output for each test,
-- allowing for easy comparison
analyzeSolvedGoals :: CC.Chan (Maybe AD.Diagnostic) -> IO ExpectedGoals
analyzeSolvedGoals chan = go emptyExpectedGoals
  where
    go observed = do
      md <- CC.readChan chan
      case md of
        Nothing -> return observed
        Just diag ->
          case diag of
            AD.DisprovedGoal {} -> go (observed { failed = failed observed + 1 })
            AD.ProvedGoal {} -> go (observed { successful = successful observed + 1 })
            _ -> go observed

-- | Create a test for a given expected output
--
-- Each expected output file records the number of goals expected to succeed and
-- fail.  We load the corresponding binary for each expected output and run the
-- verifier.  We then collect the success/failure statistics and compare them to
-- the expected output recorded in the YAML file.
--
-- NOTE: We will probably eventually want much more nuanced accounting of goals
-- to ensure that we are really seeing the failures we expect.
toTest :: FilePath -> TT.TestTree
toTest expectedOutputFile = TTH.testCase testName $ do
  expectedBytes <- BS.readFile expectedOutputFile
  expectedResult <- DY.decodeThrow expectedBytes
  binBytes <- BS.readFile binaryFilePath
  -- Create a problem instance; note that we are currently providing no
  -- arguments and no standard input.  The expected output file could include
  -- those things (or they could be drawn from other optional input files)
  let pinst = AV.ProgramInstance { AV.piPath = binaryFilePath
                                 , AV.piBinary = binBytes
                                 , AV.piStdin = Nothing
                                 , AV.piSolver = AS.Yices
                                 , AV.piFloatMode = AS.Real
                                 , AV.piCommandLineArguments = []
                                 }

  chan <- CC.newChan
  logger <- CCA.async (analyzeSolvedGoals chan)
  AV.verify (logAction chan) pinst

  CC.writeChan chan Nothing
  res <- CCA.wait logger
  TTH.assertEqual "Expected Output" expectedResult res
  where
    testName = SF.dropExtension expectedOutputFile
    binaryFilePath = testName

main :: IO ()
main = do
  testExpectedOutputs <- SFG.namesMatching "tests/binaries/*.expected"
  TT.defaultMain $ TT.testGroup "VerifierTests" (map toTest testExpectedOutputs)