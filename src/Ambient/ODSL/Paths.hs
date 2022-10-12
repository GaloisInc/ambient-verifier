-- | Various file paths to @overrides-dsl@ files and directories, which are
-- consulted in "Ambient.ODSL.EmbeddedData". Ideally, we'd just put these
-- directly in "Ambient.ODSL.EmbeddedData", but that would trip up GHC
-- staging restrictions.
module Ambient.ODSL.Paths
  ( odslIncludesDir
  , odslCrucibleHeaderPath
  ) where

import System.FilePath ( (</>) )

odslIncludesDir :: FilePath
odslIncludesDir = "submodules" </> "overrides-dsl" </> "includes"

odslCrucibleHeaderPath :: FilePath
odslCrucibleHeaderPath = "crucible.h"
