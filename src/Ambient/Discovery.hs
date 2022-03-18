{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

-- | Functions for running the macaw code discovery on a binary
--
-- Ideally, the initial and incremental code discovery logic can be maintained
-- entirely within this module without details leaking to other subsystems.
module Ambient.Discovery (
    DiscoveryBinaryType(..)
  , discoverFunctions
  , symbolMap
  ) where

import           Control.Lens ( (&), (.~) )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Maybe ( maybeToList )
import qualified Lumberjack as LJ

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Utils.IncComp as DMUI

import qualified Ambient.Diagnostic as AD

-- | Extract any available symbols from the 'DMB.LoadedBinary'
symbolMap
  :: (DMB.BinaryLoader arch binFmt)
  => DMB.LoadedBinary arch binFmt
  -> DMD.AddrSymMap (DMC.ArchAddrWidth arch)
symbolMap bin =
  Map.fromList [ (addr, symName)
               | addr <- maybe [] F.toList (DMB.entryPoints bin)
               , symName <- maybeToList (DMB.symbolFor bin (DMM.segoffAddr addr))
               ]

-- | We pass this log function to macaw to wrap discovery events in a custom
-- wrapper that we stream out with the rest of our diagnostics.
--
-- The default logger in macaw just prints to stderr, which is not very helpful
logDiscoveryEvent
  :: ( MonadIO m
     , DMM.MemWidth w
     , DMC.ArchConstraints arch
     , w ~ DMC.RegAddrWidth (DMC.ArchReg arch) )
  => LJ.LogAction IO AD.Diagnostic
  -> DMD.AddrSymMap w
  -> DMD.DiscoveryEvent arch
  -> m ()
logDiscoveryEvent logAction symMap evt =
  liftIO $ LJ.writeLog logAction (AD.DiscoveryEvent symMap evt)

-- | The type of binary for which code discovery should be performed.
data DiscoveryBinaryType arch
  = -- | The main binary containing the entry point function.
    MainBinary
      -- If @'Just' addr@, the user specified the entry point to be at this
      -- address, so perform some extra analysis to discover this function in
      -- case the binary lacks symbols (e.g., for stripped binaries).
      -- If 'Nothing', the entry point will be looked up by name later, so
      -- don't perform any extra analysis during code discovery.
      (Maybe (DMC.ArchSegmentOff arch))

  | -- | A shared library that the main binary may dynamically load.
    SharedLibrary

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
  -> DiscoveryBinaryType arch
  -> DMB.LoadedBinary arch binFmt
  -> m (DMD.DiscoveryState arch)
discoverFunctions logAction archInfo binaryType loadedBinary = do
  let mem = DMB.memoryImage loadedBinary
  let symMap = symbolMap loadedBinary
  let entryPoints0 = DMD.MayReturnFun <$ symMap
  let entryPoints1
        | -- If we are analyzing a main binary whose entry point is a
          -- user-specified address, treat it as a trusted function entry
          -- point. This will help macaw discover it in the event that the
          -- binary lacks symbols (e.g., for stripped binaries).
          MainBinary (Just addr) <- binaryType
        = Map.insert addr DMD.MayReturnFun entryPoints0
        | otherwise
        = entryPoints0
  let unexploredFunctions
        | -- Similarly, treat the address as an unexplored function.
          MainBinary (Just addr) <- binaryType
        = Map.singleton addr DMD.UserRequest
        | otherwise
        = Map.empty
  let s0 = DMD.emptyDiscoveryState mem symMap archInfo
             & DMD.trustedFunctionEntryPoints .~ entryPoints1
             & DMD.unexploredFunctions .~ unexploredFunctions
  DMA.withArchConstraints archInfo $ do
    DMUI.processIncCompLogs (logDiscoveryEvent logAction symMap) $ DMUI.runIncCompM $ do
      let discoveryOpts = DMD.defaultDiscoveryOptions
      DMD.incCompleteDiscovery s0 discoveryOpts
