module Options (
    Options(..)
  , parser
  ) where

import qualified Data.Text as T
import           Data.Word ( Word64 )
import qualified Options.Applicative as OA
import           Text.Read (readMaybe)

import qualified Ambient.Solver as AS
import qualified Ambient.Timeout as AT

-- | The options structure for the command line interface to the verifier
data Options =
  Options { binaryPath :: FilePath
          -- ^ The path to the binary to verify
          , standardInputPath :: Maybe FilePath
          -- ^ The path to a file that contains the standard input that should
          -- be fed to the binary as it is being verified
          --
          -- If this is absent, no standard input will be provided
          --
          -- See Note [Future Improvements]
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
          , weirdMachineEntries :: [Word64]
          -- ^ The entry points to any weird machines that are expected to be
          -- encountered
          }
  deriving ( Show )

-- | Parse a string representation of an integer number of seconds into an
-- AT.Timeout
timeoutReader :: String -> Maybe AT.Timeout
timeoutReader str =
  case readMaybe str of
    Nothing -> Nothing
    Just x  -> Just (AT.Seconds x)

-- | A parser for the 'Options' type
parser :: OA.Parser Options
parser = Options <$> OA.strOption ( OA.long "binary"
                                  <> OA.metavar "FILE"
                                  <> OA.help "The path to the binary to verify"
                                  )
                 <*> OA.optional (OA.strOption ( OA.long "stdin"
                                               <> OA.metavar "FILE"
                                               <> OA.help "The path to a file containing the stdin for the process"
                                               ))
                 <*> OA.many (OA.strOption ( OA.long "argv"
                                           <> OA.metavar "STRING"
                                           <> OA.help "A command line argument to pass to the process"))
                 <*> OA.option OA.auto ( OA.long "solver"
                                         <> OA.value AS.Yices
                                         <> OA.showDefault
                                         <> OA.metavar "SOLVER"
                                         <> OA.help "The solver to use for solving goals (including path satisfiability checking)"
                                       )
                 <*> OA.option OA.auto ( OA.long "float-mode"
                                         <> OA.value AS.Real
                                         <> OA.showDefault
                                         <> OA.metavar "FLOAT-MODE"
                                         <> OA.help "The interpretation of floating point operations at the SMT level"
                                       )
                 <*> OA.option (OA.maybeReader timeoutReader)
                               ( OA.long "timeout"
                                 <> OA.value AT.defaultTimeout
                                 <> OA.showDefault
                                 <> OA.metavar "SECONDS"
                                 <> OA.help "The solver timeout to use for each goal"
                               )
                 <*> OA.many (OA.option OA.auto ( OA.long "weird-machine-entry"
                                                <> OA.metavar "ADDRESS"
                                                <> OA.help ""
                                                ))

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
