-- | The main entry point of the AMBIENT binary verifier
module Ambient.Verifier (
    ProgramInstance(..)
  , verify
  ) where

import qualified Data.ByteString as BS
import qualified Lumberjack as LJ

import qualified Ambient.Diagnostic as AD

-- | A definition of the initial state of a program to be verified
--
-- Currently, this just defines the /concrete/ initial state of the
-- program. This will be extended later to support explicitly symbolic initial
-- states.
data ProgramInstance =
  ProgramInstance { piBinary :: BS.ByteString
                  -- ^ The contents of the binary to verify, which will be
                  -- parsed and lifted into the verification IR
                  , piStdin :: Maybe BS.ByteString
                  -- ^ The contents to be passed to the program via standard
                  -- input, which can be empty
                  , piCommandLineArguments :: [BS.ByteString]
                  -- ^ The command line arguments to pass to the program
                  --
                  -- The caller should ensure that this includes argv[0] (the
                  -- program name)
                  --
                  -- Note that the command line UI can take textual arguments;
                  -- the real arguments here are 'BS.ByteString's because that
                  -- is how they must be represented in the memory model.
                  }
  deriving (Show)

-- | Verify that the given 'ProgramInstance' terminates (with the given input)
-- without raising an error
verify
  :: LJ.LogAction IO AD.Diagnostic
  -> ProgramInstance
  -> IO ()
verify logAction pinst = return ()
