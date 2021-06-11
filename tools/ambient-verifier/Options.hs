module Options (
    Options(..)
  , parser
  ) where

import qualified Options.Applicative as OA

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
          , commandLineArguments :: [String]
          -- ^ A list of command line arguments to set up in the environment of
          -- the program (this should include argv[0] as the command name
          --
          -- See Note [Future Improvements]
          }
  deriving ( Show )

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

-}
