-- | The main entry point of the AMBIENT binary verifier
module Ambient.Verifier (
    ProgramInstance(..)
  , verify
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString as BS
import qualified Lumberjack as LJ

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Utils.IncComp as DMUI

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Loader as AL

-- | A definition of the initial state of a program to be verified
--
-- Currently, this just defines the /concrete/ initial state of the
-- program. This will be extended later to support explicitly symbolic initial
-- states.
data ProgramInstance =
  ProgramInstance { piPath :: Maybe FilePath
                  -- ^ The path to the binary on disk, if any
                  --
                  -- This could be none if the binary is only provided as bytes
                  -- e.g., over the network, without metadata
                  , piBinary :: BS.ByteString
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

logDiscoveryEvent
  :: (MonadIO m, DMM.MemWidth w)
  => LJ.LogAction IO AD.Diagnostic
  -> DMD.AddrSymMap w
  -> DMD.DiscoveryEvent w
  -> m ()
logDiscoveryEvent logAction symMap evt =
  liftIO $ LJ.writeLog logAction (AD.DiscoveryEvent symMap evt)

-- | Verify that the given 'ProgramInstance' terminates (with the given input)
-- without raising an error
verify
  :: (MonadIO m, CMC.MonadThrow m)
  => LJ.LogAction IO AD.Diagnostic
  -- ^ A logger to report diagnostic information to the caller
  -> ProgramInstance
  -- ^ A description of the program (and its configuration) to verify
  -> m ()
verify logAction pinst = do
  AL.withBinary (piPath pinst) (piBinary pinst) $ \archInfo loadedBinary -> do
    let mem = DMB.memoryImage loadedBinary
    let symMap = AL.symbolMap loadedBinary
    let s0 = DMD.emptyDiscoveryState mem symMap archInfo
    s1 <- DMA.withArchConstraints archInfo $ do
      DMUI.processIncCompLogs (logDiscoveryEvent logAction symMap) $ DMUI.runIncCompM $ do
        let discoveryOpts = DMD.defaultDiscoveryOptions
        DMD.incCompleteDiscovery s0 discoveryOpts
    return ()
