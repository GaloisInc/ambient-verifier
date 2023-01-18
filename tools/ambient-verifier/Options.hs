module Options (
    VerifyOptions(..)
  , TestOverridesOptions(..)
  , Command(..)
  , parser
  ) where

import qualified Data.String as Str
import qualified Data.Text as T
import           Data.Word ( Word64 )
import qualified Options.Applicative as OA
import qualified Text.Megaparsec as TM
import           Text.Read (readMaybe)

import qualified Ambient.ABI as AA
import qualified Ambient.EntryPoint as AEp
import qualified Ambient.EnvVar as AEnv
import qualified Ambient.Memory as AM
import qualified Ambient.Solver as AS
import qualified Ambient.Timeout as AT

-- | The options structure for the command line interface to the verifier's
-- \"verify\" subcommand
data VerifyOptions =
  VerifyOptions { binaryPath :: FilePath
                -- ^ The path to the binary to verify
                , fsRoot :: Maybe FilePath
                -- ^ Path to the symbolic filesystem.  If this is 'Nothing', the file
                -- system will be empty.
                --
                -- See also @Note [Future Symbolic IO Improvements]@.
                , commandLineArgv0 :: Maybe T.Text
                -- ^ If @'Just' arg@, use @arg@ as the first element of @argv@
                -- when simulating a @main(...)@ function. If 'Nothing', use
                -- @binaryPath@ instead.
                --
                -- See @Note [Simulating main()]@.
                , commandLineArguments :: [T.Text]
                -- ^ A list of command line arguments to set up in the environment of
                -- the program. Note that this excludes the command name
                -- (i.e., @argv[0]@), which is handled separately in
                -- 'commandLineArgv0'.
                --
                -- See @Note [Simulating main()]@.
                , concreteEnvVars :: [AEnv.ConcreteEnvVar T.Text]
                -- ^ A list of environment variables to set up when simulating
                --   the program, where the values are concrete.
                , concreteEnvVarsFromBytes :: [AEnv.ConcreteEnvVarFromBytes T.Text]
                -- ^ A list of environment variables to set up when simulating
                --   the program, where the values are concrete bytes contained
                --   in a file.
                , symbolicEnvVars :: [AEnv.SymbolicEnvVar T.Text]
                -- ^ A list of environment variables to set up when simulating
                --   the program, where the values are symbolic.
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
                , entryPoint :: AEp.EntryPoint
                -- ^ Where to begin simulation
                , memoryModel :: AM.MemoryModel ()
                -- ^ Which memory model configuration to use
                , profileTo :: Maybe FilePath
                -- ^ Optional directory to write profiler-related files to
                , overrideDir :: Maybe FilePath
                -- ^ Path to the crucible syntax overrides directory.  If this is
                -- 'Nothing', then no crucible syntax overrides will be registered.
                , iterationBound :: Maybe Word64
                -- ^ If @'Just' n@, bound all loops to at most @n@ iterations.
                -- If 'Nothing', do not bound the number of loop iterations.
                , recursionBound :: Maybe Word64
                -- ^ If @'Just' n@, bound the number of recursive calls to at
                -- most @n@ calls. If 'Nothing', do not bound the number of
                -- recursive calls.
                , solverInteractionFile :: Maybe FilePath
                -- ^ Optional location to write solver interactions log to
                , solverDebugMessagesFile :: Maybe FilePath
                -- ^ Optional location to write What4 solver debug messages to
                , functionCFGsFile :: Maybe FilePath
                -- ^ Optional location to write function CFGs to
                , logSymbolicBranches :: Maybe FilePath
                -- ^ Optional file to record symbolic branches to
                , logFunctionCalls :: Maybe FilePath
                -- ^ Optional file to record function call information to
                , sharedObjectDir :: Maybe FilePath
                -- ^ Directory containing shared objects to verify
                , metricsFile :: Maybe FilePath
                -- ^ File to write metrics to
                , cCompiler :: FilePath
                -- ^ The C compiler to use to preprocess C overrides
                , logObservableEvents :: Maybe FilePath
                -- ^ Optional file to log observable events occurring after
                -- a weird machine entry.
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
                       , testMemoryModel :: AM.MemoryModel ()
                       -- ^ Which memory model configuration to use
                       , testCCompiler :: FilePath
                       -- ^ The C compiler to use to preprocess C overrides
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

-- | A parser for an 'AEp.EntryPoint', which may be supplied by way of the
-- @--entry-point-name@ or @--entry-point-addr@ options.
entryPointParser :: OA.Parser AEp.EntryPoint
entryPointParser =
         AEp.EntryPointName <$>
           (OA.strOption
              ( OA.long "entry-point-name"
             <> OA.metavar "STRING"
             <> OA.help "The name of the function at which to begin simulation"
              ))
  OA.<|> AEp.EntryPointAddr <$>
           (OA.option OA.auto
               ( OA.long "entry-point-addr"
              <> OA.metavar "ADDR"
              <> OA.help (unlines
                   [ "The address of the function at which to begin simulation."
                   , "Addresses may be in hexadecimal, octal, or decimal."
                   ])
               ))
  OA.<|> pure AEp.DefaultEntryPoint

-- | A parser for a 'AM.MemoryModel', which may be supplied by way of the
-- @--memory-model@ option.
memoryModelParser :: OA.Parser (AM.MemoryModel ())
memoryModelParser =
  OA.option (mkEnvVarReader AM.memoryModelParser)
            ( OA.long "memory-model"
           <> OA.metavar "MODEL-NAME"
           <> OA.help (unlines
                [ "The memory model configuration to use. MODEL-NAME must be one"
                , "of the following:"
                , ""
                , "* default"
                , "* bump-allocator"
                , ""
                , "See the verifier README for detailed explanantions of each of"
                , "these configurations."
                ]))

-- | A parser for the @--overrides@ option
overridesParser :: OA.Parser FilePath
overridesParser = OA.strOption (  OA.long "overrides"
                               <> OA.metavar "DIRECTORY"
                               <> OA.help "A path to a directory of overides in crucible syntax to test"
                               )

-- | A paser for the @--with-gcc@ option
withCCParser :: OA.Parser FilePath
withCCParser =
  OA.strOption ( OA.long "with-cc"
              <> OA.metavar "PATH"
              <> OA.value "gcc"
              <> OA.help "The C compiler to use to preprocess C overrides (default: gcc)"
               )

-- | A parser for the \"verify\" subcommand
verifyParser :: OA.Parser Command
verifyParser = Verify <$> verifyOptions

-- | Convert a @megaparsec@ parser to an @optparse-applicative@ 'OA.ReadM'.
mkEnvVarReader ::
     ( TM.ShowErrorComponent e
     , Str.IsString s
     , TM.VisualStream s
     , TM.TraversableStream s
     )
  => TM.Parsec e s a -> OA.ReadM a
mkEnvVarReader p = OA.eitherReader $ \rawStr ->
  case TM.parse p "" (Str.fromString rawStr) of
    Left err  -> Left $ TM.errorBundlePretty err
    Right val -> Right val

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
           <*> OA.optional (OA.strOption ( OA.long "argv0"
                                        <> OA.metavar "STRING"
                                        <> OA.help (unlines
                                             [ "The first command line argument to pass to the process"
                                             , "(i.e., argv[0]). If not specified, this will default to"
                                             , "the --binary path."
                                             ])
                                         ))
           <*> OA.many (OA.strOption ( OA.long "argument"
                                     <> OA.metavar "STRING"
                                     <> OA.help (unlines
                                          [ "A command line argument to pass to the process. This can be"
                                          , "supplied multiple times to pass multiple arguments."
                                          ])
                                    ))
           <*> OA.many (OA.option (mkEnvVarReader AEnv.concreteEnvVarParser)
                                  ( OA.long "env-var"
                                 <> OA.metavar "KEY=VALUE"
                                 <> OA.help (unlines
                                       [ "Define a environment variable named KEY with the"
                                       , "concrete value VALUE for the duration of the process."
                                       , "This can be supplied multiple times to define"
                                       , "multiple environment variables."
                                       ])
                                 ))
           <*> OA.many (OA.option (mkEnvVarReader AEnv.concreteEnvVarFromBytesParser)
                                  ( OA.long "env-var-from-bytes"
                                 <> OA.metavar "KEY[FILE]"
                                 <> OA.help (unlines
                                       [ "Define a environment variable named KEY with a"
                                       , "concrete value for the duration of the process,"
                                       , "where the value consists of the bytes of FILE's"
                                       , "contents. This can be supplied multiple times to"
                                       , "define multiple environment variables."
                                       ])
                                 ))
           <*> OA.many (OA.option (mkEnvVarReader AEnv.symbolicEnvVarParser)
                                  ( OA.long "env-var-symbolic"
                                 <> OA.metavar "KEY[LEN]"
                                 <> OA.help (unlines
                                       [ "Define a environment variable named KEY with a"
                                       , "value containing LEN symbolic characters (plus a"
                                       , "null terminator) for the duration of the process."
                                       , "This can be supplied multiple times to define"
                                       , "multiple symbolic environment variables."
                                       ])
                                 ))
           <*> solverParser
           <*> floatModeParser
           <*> timeoutParser
           <*> OA.many (OA.strOption ( OA.long "statechart"
                                    <> OA.metavar "FILE"
                                    <> OA.help "A path to a state chart encoding a property to verify"
                                     ))
           <*> entryPointParser
           <*> memoryModelParser
           <*> OA.optional (OA.strOption ( OA.long "profile-to"
                                      <> OA.metavar "DIR"
                                      <> OA.help (unlines
                                           [ "Periodically log symbolic execution profiles to DIR."
                                           , "Open 'DIR/profile.html' to view an HTML report of the profiles."
                                           ])
                                       ))
           <*> OA.optional overridesParser
           <*> OA.optional (OA.option OA.auto
                                      ( OA.long "iteration-bound"
                                     <> OA.metavar "NUM"
                                     <> OA.help "Bound all loops to at most this many iterations"
                                      ))
           <*> OA.optional (OA.option OA.auto
                                      ( OA.long "recursion-bound"
                                     <> OA.metavar "NUM"
                                     <> OA.help "Bound the number of recursive calls to at most this many calls"
                                      ))
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
           <*> OA.optional (OA.strOption ( OA.long "log-symbolic-branches"
                                        <> OA.metavar "FILE"
                                        <> OA.help "Log all symbolic branches that occur to FILE"
                                       ))
           <*> OA.optional (OA.strOption ( OA.long "log-function-calls"
                                        <> OA.metavar "FILE"
                                        <> OA.help "Log each the name and address of each function call to FILE"
                                       ))
           <*> OA.optional (OA.strOption ( OA.long "shared-objects"
                                        <> OA.short 'L'
                                        <> OA.metavar "DIRECTORY"
                                        <> OA.help (unlines
                                             [ "Directory containing shared objects to verify."
                                             , "The default value is the directory in which the main binary lives."
                                             , "If the program you are verifying attempts to invoke a function in"
                                             , "a shared library that not in this directory, then the verifier"
                                             , "will fail unless an override is supplied for that function."
                                             ])))
           <*> OA.optional (OA.strOption ( OA.long "metrics"
                                        <> OA.metavar "FILE"
                                        <> OA.help "File to write metrics to"))
           <*> withCCParser
           <*> OA.optional (OA.strOption ( OA.long "log-observable-events"
                                        <> OA.metavar "FILE"
                                        <> OA.help "Log observable events occurring after a weird machine entry to FILE"
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
           <*> memoryModelParser
           <*> withCCParser
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

{-
Note [Future Symbolic IO Improvements]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In the future, some options related to symbolic IO will need to be extended to
be more expressive.

The contents of standard input will always be necessary (or at least
supported). This will likely need to be generalized to support:
- many more input/output sources (e.g., files, sockets)
- environment variables
- symbolic contents of each (currently, only concrete values are supported)

Note [Simulating main()]
~~~~~~~~~~~~~~~~~~~~~~~~
When simulating an entry point, we assume it has the same type signature as one
of `int main()`, `int main(int argc, char *argv[])`, or
`int main(int argc, char *argv[], char *envp[])`. In case `main` accepts
arguments, we need to pre-populate the registers corresponding to `argc`,
`argv`, and `envp` to ensure that simulation works as expected. (We aren't
strictly required to do so in the event that `main` doesn't accept some of
these arguments, but we do so anyway, as it does no harm and avoids us having to
figure out which type of main() function we're in.)

After obtaining the arguments from the command line, we have to marshal them to
the appropriate C values. This process is quite straightfoward for `argc`, but
`argv` and `envp` are a bit trickier. Let's start with `argv` first. The user
provides the values in `argv` as [Text], but in C, `argv` is represented as an
array of C strings. To convert from the former to the latter, we need to do the
following:

* We need to convert each Text value to a ByteString, which corresponds closely
  to C's representation of a string (i.e., an array of bytes). We must also
  pick an encoding to use—see Note [Argument Encoding] in A.Encoding.
* Next, we need to store each ByteString in memory as an array of `char`s. In
  Crucible terms, a Vector of LLVMPtrs. To do so, we stack-allocate a pointer
  with number of bytes equal to (the length of the ByteString) + 1. The (+ 1)
  is needed because in addition to storing each byte in the ByteString, we must
  also store a null terminator at the end to make it a legal C string. We
  leverage the crucible-llvm memory model's doAlloca and doStore functions to
  do the heavy lifting here—see `allocaCString` in
  A.Verifier.SymbolicExecution for how they're used.
* Finally, we need to store the overall @argv@ array in memory as an array of
  C strings. Again, this looks like a Vector of LLVMPtrs in Crucible, but this
  time the LLVMPtrs represent C pointers rather than C `char`s. We again
  stack-allocate a pointer, this time with space equal to
  (the pointer width) × (argc + 1). The (+ 1) is needed here because section
  5.1.2.2.1 of the C standard requires argv[argc] to be a null pointer. So we
  follow the rules and write each of the C string pointers from the previous
  step to memory, followed by a trailing null pointer. See `allocaArgv` in
  A.Verifier.SymbolicExecution` for how this is implemented.

Once we've done all that, all that's left is to update the appropriate
registers. Because these will be different on each OS/architecture
configuration, we abstract out the values of these registers into the
`functionIntegerArgumentRegisters` field of a `FunctionABI`.

The process for `envp` is largely similar to that of `argv`, as `envp` is also
an array of C strings. See `allocaEnvp` in A.Verifier.SymbolicExecution for the
implementation. The primary differences between the handling of `argv` and
`envp` are that:

* Each element of `envp` is in `KEY=VALUE` format. Moreover, we ensure that
  each `KEY` is only present in one element of `envp`, i.e., there are no
  duplicate keys.

* Environment variable `VALUE`s can be made symbolic by using the
  --env-var-symbolic KEY[n] command-line option, where KEY is assigned a
  VALUE of `n` symbolic characters, followed by a null terminator.

Be aware of the following limitations:

* The command line parameters specifying `argv` are currently concrete. We may
  want them to be symbolic at some point. In particular, we might be interested
  in whether or not argv[0] is absolute or relative.  In that example, we could
  improve our diagnostics by just making argv[0] a mux on a fresh boolean
  variable that we record; if it is referenced in a counterexample, that would
  tell us that the condition is important for explaining a failure.

* Command line parameters are currently text; if we need to support
  binary data in command line arguments, that should be done through a separate
  (alternative) file-based mechanism.

* All of this machinery assumes that main()—or, a function with a type
  signature like main()—is the entry point. This would not work at all if
  _start() were the entry point, as that uses a completely different mechanism
  for populating the arguments. See Note [Entry Point] in A.Verifier.
-}
