module Ambient.Memory.AArch32.Linux (
    aarch32LinuxInitGlobals
  , aarch32LinuxStmtExtensionOverride
  ) where

import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.ARM as DMA
import qualified Lang.Crucible.Simulator.GlobalState as LCSG

import qualified Ambient.Memory as AM

-- | AArch32 does not require any ghost globals
aarch32LinuxInitGlobals :: AM.InitArchSpecificGlobals DMA.ARM
aarch32LinuxInitGlobals =
  AM.InitArchSpecificGlobals $ \_sym mem0 -> return (mem0, LCSG.emptyGlobals)

-- | There are currently no overrides for macaw-aarch32-symbolic
aarch32LinuxStmtExtensionOverride :: DMS.MacawArchStmtExtensionOverride DMA.ARM
aarch32LinuxStmtExtensionOverride =
  DMS.MacawArchStmtExtensionOverride $ \_ _ -> return Nothing
