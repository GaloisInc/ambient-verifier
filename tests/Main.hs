{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
module Main ( main ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import qualified Data.Set as Set
import qualified Data.Yaml as DY
import           GHC.Generics ( Generic )
import qualified Lumberjack as LJ
import qualified System.FilePath as SF
import qualified System.FilePath.Glob as SFG
import qualified Test.Tasty as TT
import qualified Test.Tasty.ExpectedFailure as TTE
import qualified Test.Tasty.HUnit as TTH

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Solver as AS
import qualified Ambient.Timeout as AT
import qualified Ambient.Verifier as AV

data ExpectedGoals =
  ExpectedGoals { successful :: Int
                , failed :: Int
                , wmTargets :: Set.Set Integer
                , fsRoot :: Maybe FilePath
                }
  deriving (Eq, Ord, Read, Show, Generic)

instance DY.FromJSON ExpectedGoals

emptyExpectedGoals :: ExpectedGoals
emptyExpectedGoals = ExpectedGoals { successful = 0
                                   , failed = 0
                                   , wmTargets = Set.empty
                                   , fsRoot = Nothing
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
                                 , AV.piFsRoot = fsRoot expectedResult
                                 , AV.piSolver = AS.Yices
                                 , AV.piFloatMode = AS.Real
                                 , AV.piCommandLineArguments = []
                                 , AV.piWeirdMachineEntries = fmap fromIntegral (F.toList (wmTargets expectedResult))
                                 }

  chan <- CC.newChan
  logger <- CCA.async (analyzeSolvedGoals chan)
  AV.verify (logAction chan) pinst AT.defaultTimeout

  CC.writeChan chan Nothing
  res <- CCA.wait logger

  -- This is a bit odd since we are using the .expected file to specify both the
  -- expected result and the list of candidate Weird Machine targets
  -- (wmTargets), so we just copy the targets over to make the comparison work
  -- out.  Similarly, we also copy 'fsRoot' over.
  let res' = res { wmTargets = wmTargets expectedResult
                 , fsRoot = fsRoot expectedResult
                 }
  TTH.assertEqual "Expected Output" expectedResult res'
  where
    testName = SF.dropExtension expectedOutputFile
    binaryFilePath = testName

-- | Create a test that is expected to fail for a given output
--
-- See the documentation for 'toTest' for details on the contents of the
-- expected output file.
toFailingTest :: FilePath -> TT.TestTree
toFailingTest = TTE.expectFail . toTest

main :: IO ()
main = do
  testExpectedOutputs <- SFG.namesMatching "tests/binaries/*.expected"
  failingTestExpectedOutputs <- SFG.namesMatching
                                "tests/binaries/*.expected-failing"
  TT.defaultMain $ TT.testGroup
                   "VerifierTests"
                   (concat [ map toTest testExpectedOutputs
                           , map toFailingTest failingTestExpectedOutputs
                           ])
