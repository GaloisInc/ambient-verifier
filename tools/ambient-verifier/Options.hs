module Options (
    VerifyOptions(..)
  , TestOverridesOptions(..)
  , Command(..)
  , parser
  ) where

import qualified Data.Text as T
import qualified Options.Applicative as OA
import           Text.Read (readMaybe)

import qualified Ambient.ABI as AA
import qualified Ambient.Solver as AS
import qualified Ambient.Timeout as AT

-- | The options structure for the command line interface to the verifier's
-- \"verify\" subcommand
data VerifyOptions =
  VerifyOptions { binaryPath :: FilePath
                -- ^ The path to the binary to verify
                , fsRoot :: Maybe FilePath
                -- ^ Path to the symbolic filesystem.  If this is 'Nothing', the file
                -- system will be empty
                , commandLineArguments :: [T.Text]
                -- ^ A list of command line arguments to set up in the environment of
                -- the program (this should include argv[0] as the command name)
                --
                -- See Note [Future Improvements]
                , solver :: AS.Solver
                -- ^ The SMT solver to use for path satisfiability checking and
                -- discharging verification conditions
                , floatMode :: AS.FloatMode
                -- ^ The interpretation of floating point values to use during both
                -- path satisfiability checking and discharging verification conditions
                , timeoutDuration :: AT.Timeout
                -- ^ The solver timeout for each goal
                , stateCharts :: [FilePath]
                -- ^ File paths to a state charts encoding properties to verify
                , profileTo :: Maybe FilePath
                -- ^ A path to write periodic profiling reports to
                , overrideDir :: Maybe FilePath
                -- ^ Path to the crucible syntax overrides directory.  If this is
                -- 'Nothing', then no crucible syntax overrides will be registered.
                , solverInteractionFile :: Maybe FilePath
                -- ^ Optional location to write solver interactions log to
                , solverDebugMessagesFile :: Maybe FilePath
                -- ^ Optional location to write What4 solver debug messages to
                , functionCFGsFile :: Maybe FilePath
                -- ^ Optional location to write function CFGs to
                }
  deriving ( Show )

-- | The options structure for the command line interface to the verifier's
-- \"test-overrides\" subcommand
data TestOverridesOptions =
  TestOverridesOptions { testOverrideDir :: FilePath
                       -- ^ Path to the crucible syntax overrides directory
                       , testAbi :: AA.ABI
                       -- ^ ABI to use when running tests
                       , testSolver :: AS.Solver
                       -- ^ The SMT solver to use for path satisfiability
                       -- checking and discharging verification conditions
                       , testFloatMode :: AS.FloatMode
                       -- ^ The interpretation of floating point values to use
                       -- during both path satisfiability checking and
                       -- discharging verification conditions
                       , testTimeoutDuration :: AT.Timeout
                       -- ^ The solver timeout for each goal
                       }

-- | The options structure for the command line interface to the verifier
data Command
  = Verify VerifyOptions
  | ListOverrides VerifyOptions
  | TestOverrides TestOverridesOptions

-- | Parse a string representation of an integer number of seconds into an
-- AT.Timeout
timeoutReader :: String -> Maybe AT.Timeout
timeoutReader str =
  case readMaybe str of
    Nothing -> Nothing
    Just x  -> Just (AT.Seconds x)

-- | A parser for the @--solver@ option
solverParser :: OA.Parser AS.Solver
solverParser = OA.option OA.auto ( OA.long "solver"
                                <> OA.value AS.Yices
                                <> OA.showDefault
                                <> OA.metavar "SOLVER"
                                <> OA.help "The solver to use for solving goals (including path satisfiability checking)"
                                 )

-- | A parser for the @--float-mode@ option
floatModeParser :: OA.Parser AS.FloatMode
floatModeParser =  OA.option OA.auto ( OA.long "float-mode"
                                    <> OA.value AS.Real
                                    <> OA.showDefault
                                    <> OA.metavar "FLOAT-MODE"
                                    <> OA.help "The interpretation of floating point operations at the SMT level"
                                     )

-- | A parser for the @--timeout@ option
timeoutParser :: OA.Parser AT.Timeout
timeoutParser =  OA.option (OA.maybeReader timeoutReader)
                           (  OA.long "timeout"
                           <> OA.value AT.defaultTimeout
                           <> OA.showDefault
                           <> OA.metavar "SECONDS"
                           <> OA.help "The solver timeout to use for each goal"
                           )

-- | A parser for the @--overrides@ option
overridesParser :: OA.Parser FilePath
overridesParser = OA.strOption (  OA.long "overrides"
                               <> OA.metavar "DIRECTORY"
                               <> OA.help "A path to a directory of overides in crucible syntax to test"
                               )

-- | A parser for the \"verify\" subcommand
verifyParser :: OA.Parser Command
verifyParser = Verify <$> verifyOptions

-- | The options used for the @verify@ and @list-overrides@ subcommands.
verifyOptions :: OA.Parser VerifyOptions
verifyOptions = VerifyOptions
           <$> OA.strOption ( OA.long "binary"
                            <> OA.metavar "FILE"
                            <> OA.help "The path to the binary to verify"
                            )
           <*> OA.optional (OA.strOption ( OA.long "fsroot"
                                         <> OA.metavar "FILE"
                                         <> OA.help "The path to the symbolic filesystem for the process"
                                         ))
           <*> OA.many (OA.strOption ( OA.long "argv"
                                     <> OA.metavar "STRING"
                                     <> OA.help "A command line argument to pass to the process"))
           <*> solverParser
           <*> floatModeParser
           <*> timeoutParser
           <*> OA.many (OA.strOption ( OA.long "statechart"
                                    <> OA.metavar "FILE"
                                    <> OA.help "A path to a state chart encoding a property to verify"
                                     ))
           <*> OA.optional (OA.strOption ( OA.long "profile-to"
                                      <> OA.metavar "FILE"
                                      <> OA.help "A file to log symbolic execution profiles to periodically"
                                       ))
           <*> OA.optional overridesParser
           <*> OA.optional (OA.strOption ( OA.long "log-solver-interactions"
                                        <> OA.metavar "FILE"
                                        <> OA.help "Log solver interactions to FILE"
                                       ))
           <*> OA.optional (OA.strOption ( OA.long "log-solver-debug-messages"
                                        <> OA.metavar "FILE"
                                        <> OA.help "Log What4 debug messages produced when communicating with solvers to FILE"
                                       ))
           <*> OA.optional (OA.strOption ( OA.long "log-function-cfgs"
                                        <> OA.metavar "FILE"
                                        <> OA.help "Log the control-flow graphs of functions that the verifier discovers to FILE"
                                       ))

-- | A parser for the \"list-overrides\" subcommand
listOverridesParser :: OA.Parser Command
listOverridesParser = ListOverrides <$> verifyOptions

-- | A parser for the \"test-overrides\" subcommand
testOverridesParser :: OA.Parser Command
testOverridesParser = TestOverrides <$> (TestOverridesOptions
           <$> overridesParser
           <*> OA.option OA.auto (  OA.long "abi"
                                 <> OA.metavar "ABI"
                                 <> OA.help "The ABI to use when loading crucible syntax files.  Must be 'X86_64Linux' or 'AArch32Linux'."
                                 )
           <*> solverParser
           <*> floatModeParser
           <*> timeoutParser
           )


-- | A parser for the 'Command' type
parser :: OA.Parser Command
parser = OA.subparser
  (  OA.command "verify"
                (OA.info (verifyParser OA.<**> OA.helper)
                         (OA.progDesc "Verify that the given binary with inputs terminates cleanly"))
  <> OA.command "list-overrides"
                (OA.info (listOverridesParser OA.<**> OA.helper)
                         (OA.progDesc "List the overrides that a binary can make use of"))
  <> OA.command "test-overrides"
                (OA.info (testOverridesParser OA.<**> OA.helper)
                         (OA.progDesc "Run function override tests"))

 )

{- Note [Future Improvements]

In the future, some of these options will need to be extended to be more
expressive.

The contents of standard input will always be necessary (or at least
supported). This will likely need to be generalized to support:
- many more input/output sources (e.g., files, sockets)
- environment variables
- symbolic contents of each (currently, only concrete values are supported)

The command line parameters are currently concrete. We may want them to be
symbolic at some point. In particular, we might be interested in whether or not
argv[0] is absolute or relative.  In that example, we could improve our
diagnostics by just making argv[0] a mux on a fresh boolean variable that we
record; if it is referenced in a counterexample, that would tell us that the
condition is important for explaining a failure.

Note that command line parameters are currently text; if we need to support
binary data in command line arguments, that should be done through a separate
(alternative) file-based mechanism.

-}
