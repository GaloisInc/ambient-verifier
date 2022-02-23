{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
module Main ( main ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Data.ByteString as BS
import qualified Data.List as List
import           Data.Maybe ( maybeToList )
import qualified Data.Yaml as DY
import           GHC.Generics ( Generic )
import qualified Lumberjack as LJ
import qualified System.Directory as SD
import qualified System.FilePath as SF
import qualified System.FilePath.Glob as SFG
import qualified Test.Tasty as TT
import qualified Test.Tasty.Runners.AntXML as TTRA
import qualified Test.Tasty.ExpectedFailure as TTE
import qualified Test.Tasty.HUnit as TTH

import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.Syntax.Concrete as LCSC

import qualified Ambient.ABI as AA
import qualified Ambient.Diagnostic as AD
import qualified Ambient.OverrideTester as AO
import qualified Ambient.Property.Definition as APD
import qualified Ambient.Solver as AS
import qualified Ambient.Timeout as AT
import qualified Ambient.Verifier as AV

data ExpectedGoals =
  ExpectedGoals { successful :: Int
                , failed :: Int
                , fsRoot :: Maybe FilePath
                , overrideDir :: Maybe FilePath
                }
  deriving (Eq, Ord, Read, Show, Generic)

instance DY.FromJSON ExpectedGoals

emptyExpectedGoals :: ExpectedGoals
emptyExpectedGoals = ExpectedGoals { successful = 0
                                   , failed = 0
                                   , fsRoot = Nothing
                                   , overrideDir = Nothing
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

loadProperty :: FilePath -> IO (APD.Property APD.StateID)
loadProperty fp = do
  bytes <- BS.readFile fp
  val <- DY.decodeThrow bytes
  APD.parseProperty val

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

  let propPath = SF.replaceExtension expectedOutputFile "yaml"
  propFileExists <- SD.doesFileExist propPath
  mprop <- case propFileExists of
             True -> Just <$> loadProperty propPath
             False -> return Nothing

  -- Create a problem instance; note that we are currently providing no
  -- arguments and no standard input.  The expected output file could include
  -- those things (or they could be drawn from other optional input files)
  let pinst = AV.ProgramInstance { AV.piPath = binaryFilePath
                                 , AV.piBinary = binBytes
                                 , AV.piFsRoot = fsRoot expectedResult
                                 , AV.piSolver = AS.Yices
                                 , AV.piFloatMode = AS.Real
                                 , AV.piCommandLineArguments = []
                                 , AV.piProperties = maybeToList mprop
                                 , AV.piProfileTo = Nothing
                                 , AV.piOverrideDir = overrideDir expectedResult
                                 , AV.piSolverInteractionFile = Nothing
                                 }

  chan <- CC.newChan
  logger <- CCA.async (analyzeSolvedGoals chan)
  AV.verify (logAction chan) pinst AT.defaultTimeout

  CC.writeChan chan Nothing
  res <- CCA.wait logger

  -- This is a bit odd since we are using the expected result structure to
  -- specify both the initial state and expected state. We copy over some
  -- constants to just make the comparison work out.
  let res' = res { fsRoot = fsRoot expectedResult
                 , overrideDir = overrideDir expectedResult
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

-- | This checks that the number of failing goals matches the number of
-- override tests that end in @_failing@.  This works well for evaluating the
-- simple tests we currently have, but we may want a more robust solution if we
-- ever have more complex override tests.
overrideTestsPassed :: CC.Chan (Maybe AD.Diagnostic) -> IO Bool
overrideTestsPassed chan = do
    res <- go 0
    return (res == 0)
  where
    -- Increment 'delta' on a disproved goal, and decrement 'delta' when
    -- encountering a test function ending in @_failing@
    go :: Int -> IO (Int)
    go delta = do
      md <- CC.readChan chan
      case md of
        Nothing -> return delta
        Just diag ->
          case diag of
            AD.DisprovedGoal {} -> go (delta + 1)
            AD.ExecutingOverrideTest (LCSC.ACFG _ _ g) _ ->
              let fnName = LCF.handleName (LCCR.cfgHandle g) in
              if List.isSuffixOf "_failing" (show fnName)
              then go (delta - 1)
              else go delta
            _ -> go delta

-- | Run tests present in crucible override files
overrideTests :: AA.ABI -> TT.TestTree
overrideTests abi = TTH.testCase ((show abi) ++ " override tests") $ do
  -- Create a test instance
  let tinst = AO.TestInstance { AO.tiSolver = AS.Yices
                              , AO.tiFloatMode = AS.Real
                              , AO.tiOverrideDir = "tests/overrides"
                              , AO.tiAbi = abi
                              }

  chan <- CC.newChan
  logger <- CCA.async (overrideTestsPassed chan)
  AO.testOverrides (logAction chan) tinst AT.defaultTimeout

  CC.writeChan chan Nothing
  res <- CCA.wait logger

  TTH.assertBool "Override tests failed" res

main :: IO ()
main = do
  testExpectedOutputs <- SFG.namesMatching "tests/binaries/*/*.expected"
  failingTestExpectedOutputs <- SFG.namesMatching
                                "tests/binaries/*/*.expected-failing"
  TT.defaultMainWithIngredients
    (TTRA.antXMLRunner : TT.defaultIngredients) $
    TT.testGroup
      "VerifierTests"
      (concat [ map toTest testExpectedOutputs
              , map toFailingTest failingTestExpectedOutputs
              , map overrideTests AA.allABIs
              ])
