-- | Functions for running the macaw code discovery on a binary
--
-- Ideally, the initial and incremental code discovery logic can be maintained
-- entirely within this module without details leaking to other subsystems.
module Ambient.Discovery (
  discoverFunctions
  ) where

import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Lumberjack as LJ

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Utils.IncComp as DMUI

import qualified Ambient.Diagnostic as AD

symbolMap
  :: (DMB.BinaryLoader arch binFmt)
  => DMB.LoadedBinary arch binFmt
  -> DMD.AddrSymMap (DMC.ArchAddrWidth arch)
symbolMap = undefined

-- | We pass this log function to macaw to wrap discovery events in a custom
-- wrapper that we stream out with the rest of our diagnostics.
--
-- The default logger in macaw just prints to stderr, which is not very helpful
logDiscoveryEvent
  :: (MonadIO m, DMM.MemWidth w)
  => LJ.LogAction IO AD.Diagnostic
  -> DMD.AddrSymMap w
  -> DMD.DiscoveryEvent w
  -> m ()
logDiscoveryEvent logAction symMap evt =
  liftIO $ LJ.writeLog logAction (AD.DiscoveryEvent symMap evt)

-- | Run the code discovery procedure, streaming out diagnostics that
-- provide indications of progress.
--
-- Note that this is just the initial run; we may re-invoke code discovery later
-- if we identify call targets (via symbolic execution) that macaw did not
-- initially find.
discoverFunctions
  :: (MonadIO m, DMB.BinaryLoader arch binFmt)
  => LJ.LogAction IO AD.Diagnostic
  -> DMA.ArchitectureInfo arch
  -> DMB.LoadedBinary arch binFmt
  -> m (DMD.DiscoveryState arch)
discoverFunctions logAction archInfo loadedBinary = do
  let mem = DMB.memoryImage loadedBinary
  let symMap = symbolMap loadedBinary
  let s0 = DMD.emptyDiscoveryState mem symMap archInfo
  DMA.withArchConstraints archInfo $ do
    DMUI.processIncCompLogs (logDiscoveryEvent logAction symMap) $ DMUI.runIncCompM $ do
      let discoveryOpts = DMD.defaultDiscoveryOptions
      DMD.incCompleteDiscovery s0 discoveryOpts
