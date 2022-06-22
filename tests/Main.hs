{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main ( main ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Control.Exception as CE
import           Control.Monad ( unless )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as List
import           Data.Maybe ( fromMaybe, maybeToList )
import qualified Data.Text as DT
import qualified Data.Text.Lazy as DTL
import qualified Data.Text.Lazy.Encoding as TLE
import           Data.Word ( Word64 )
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

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.Syntax.Concrete as LCSC

import qualified Ambient.ABI as AA
import qualified Ambient.Diagnostic as AD
import qualified Ambient.Encoding as AEnc
import qualified Ambient.EntryPoint as AEp
import qualified Ambient.Exception as AE
import qualified Ambient.OverrideTester as AO
import qualified Ambient.Property.Definition as APD
import qualified Ambient.Solver as AS
import qualified Ambient.Timeout as AT
import qualified Ambient.Verifier as AV
import qualified Ambient.Verifier.Prove as AVP

data ExpectedGoals =
  ExpectedGoals { successful :: Int
                , failed :: Int
                , fsRoot :: Maybe FilePath
                , overrideDir :: Maybe FilePath
                , iterationBound :: Maybe Word64
                , recursionBound :: Maybe Word64
                , sharedObjectsDir :: Maybe FilePath
                , entryPointAddr :: Maybe Word64
                  -- We may also wish to allow specifying entry point names
                  -- in the future, but for the time being, let's keep it
                  -- simple.
                , argv0 :: Maybe DT.Text
                , arguments :: Maybe [DT.Text]
                  -- Here, Nothing denotes the empty list. We use Maybe as a
                  -- convenience for working with the Generic-based default
                  -- implementation of FromJSON for ExpectedGoals, which has
                  -- a special case for Maybe fields that allows them to be
                  -- omitted. Without the maybe, we'd have to manually specify
                  -- @arguments: []@ in nearly every *.exe.expected file, which
                  -- would be incredibly tedious.
                  --
                  -- If we ever opt to write ExpectedGoals' FromJSON instance
                  -- by hand, as proposed in #90, we could change this field
                  -- from type Maybe [Text] to just [Text] at that time.
                , throwsException :: Maybe Bool
                  -- Similar to above, Nothing represents False, as does Just False
                }
  deriving (Eq, Ord, Read, Show, Generic)

instance DY.FromJSON ExpectedGoals

emptyExpectedGoals :: ExpectedGoals
emptyExpectedGoals = ExpectedGoals { successful = 0
                                   , failed = 0
                                   , fsRoot = Nothing
                                   , overrideDir = Nothing
                                   , iterationBound = Nothing
                                   , recursionBound = Nothing
                                   , sharedObjectsDir = Nothing
                                   , entryPointAddr = Nothing
                                   , argv0 = Nothing
                                   , arguments = Nothing
                                   , throwsException = Nothing
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

data CaughtVerifyException =
    CaughtAbortExecReason LCB.AbortExecReason
  | CaughtAmbientException AE.AmbientException

showVerifyException :: CaughtVerifyException -> String
showVerifyException (CaughtAbortExecReason aer) = show aer
showVerifyException (CaughtAmbientException ae) = show ae

-- | The result of running verify
-- 
-- Either the output metrics, or a caught exception (which might
-- be acceptable if the test expects it).
data VerifyResult = 
    CaughtVerifyException CaughtVerifyException
  | VerifyOK AV.Metrics

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

  let entryPoint = maybe AEp.DefaultEntryPoint AEp.EntryPointAddr
                         (entryPointAddr expectedResult)

  let args = AEnc.encodeCommandLineArguments binaryFilePath
                                             (argv0 expectedResult)
                                             (fromMaybe [] (arguments expectedResult))

  -- Create a problem instance; note that we are currently providing no
  -- arguments and no standard input.  The expected output file could include
  -- those things (or they could be drawn from other optional input files)
  let pinst = AV.ProgramInstance { AV.piPath = binaryFilePath
                                 , AV.piBinary = binBytes
                                 , AV.piFsRoot = fsRoot expectedResult
                                 , AV.piSolver = AS.Yices
                                 , AV.piFloatMode = AS.Real
                                 , AV.piCommandLineArguments = args
                                 , AV.piProperties = maybeToList mprop
                                 , AV.piEntryPoint = entryPoint
                                 , AV.piProfileTo = Nothing
                                 , AV.piOverrideDir = overrideDir expectedResult
                                 , AV.piIterationBound = iterationBound expectedResult
                                 , AV.piRecursionBound = recursionBound expectedResult
                                 , AV.piSolverInteractionFile = Nothing
                                 , AV.piSharedObjectDir = sharedObjectsDir expectedResult
                                 , AV.piLogSymbolicBranches = Nothing
                                 }

  chan <- CC.newChan
  logger <- CCA.async (analyzeSolvedGoals chan)
  metricsOrErr <- (VerifyOK <$> AV.verify (logAction chan) pinst AT.defaultTimeout)
                    `CE.catches` [CE.Handler (\ (ex :: LCB.AbortExecReason) -> return $ CaughtVerifyException (CaughtAbortExecReason ex)),
                                  CE.Handler (\ (ex :: AE.AmbientException) -> return $ CaughtVerifyException (CaughtAmbientException ex))]

  -- If throwsException is set, catch AbortExecReason's
  let doCatchErr = fromMaybe False $ throwsException expectedResult
  if doCatchErr then
      case metricsOrErr of
        CaughtVerifyException e -> do
          handleExpectedException (showVerifyException e)
        VerifyOK _ -> do
          -- Failed! Didn't error when doCatchErr was true
          TTH.assertFailure "Exception was expected, but none were caught"
    else
      case metricsOrErr of
        CaughtVerifyException e -> do
          -- Failed! Error when doCatchErr was false
          TTH.assertFailure $ "Unexpected exception: " ++ (showVerifyException e)
        VerifyOK metrics -> do
          assertMetricsOK chan logger expectedResult metrics

  where
    testName = SF.dropExtension expectedOutputFile
    binaryFilePath = testName
    handleExpectedException exStr = do
          let exceptionPath = SF.replaceExtension expectedOutputFile "exception"
          exceptionFileExists <- SD.doesFileExist exceptionPath
          unless exceptionFileExists $
              -- We're meant to catch an exception, but no exception
              -- file exists. We should inform the user of this
              TTH.assertFailure $ "throwsException was set to true, but no .exe.exception file was found. Expected: \"" ++ exStr ++ "\""

          -- We're meant to catch an exception, and need to
          -- compare it against the exception file given.
          -- To do this, we'll just use the appropriate Show instance
          excFile <- BS.readFile exceptionPath
          let actualErr = BL.toStrict $ TLE.encodeUtf8 $ DTL.pack exStr
          -- Compare the exception file to the actual error
          TTH.assertEqual "Expected exception" excFile actualErr

    assertMetricsOK chan logger expectedResult metrics = do
        -- We weren't expecting errors, and we didn't get any
        CC.writeChan chan Nothing
        res <- CCA.wait logger

        -- This is a bit odd since we are using the expected result structure to
        -- specify both the initial state and expected state. To produce the actual
        -- result, we copy over the goal numbers, which could differ from what is
        -- expected. We leave alone the other fields, which are constants, to just
        -- make the comparison work out.
        let res' = expectedResult { successful = successful res
                                  , failed     = failed res
                                  }
        TTH.assertEqual "Expected Output" expectedResult res'

        -- Check that goal values in metrics match the expected number of goals
        let proofStats = AV.proofStats metrics
        TTH.assertEqual "Total expected number of goals"
                        (successful expectedResult + failed expectedResult)
                        (AVP.psGoals proofStats)
        TTH.assertEqual "Expected successful goals"
                        (successful expectedResult)
                        (AVP.psSuccessfulGoals proofStats)
        TTH.assertEqual "Expected failed goals"
                        (failed expectedResult)
                        (AVP.psFailedGoals proofStats)
        TTH.assertEqual "Expected timeouts" 0 (AVP.psTimeouts proofStats)
        TTH.assertEqual "Expected errors" 0 (AVP.psErrors proofStats)

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
  testExpectedOutputs <- SFG.glob "tests/binaries/**/*.expected"
  failingTestExpectedOutputs <- SFG.glob
                                "tests/binaries/**/*.expected-failing"
  TT.defaultMainWithIngredients
    (TTRA.antXMLRunner : TT.defaultIngredients) $
    TT.testGroup
      "VerifierTests"
      (concat [ map toTest testExpectedOutputs
              , map toFailingTest failingTestExpectedOutputs
              , map overrideTests AA.allABIs
              ])
