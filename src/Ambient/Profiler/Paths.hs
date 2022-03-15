-- | Various file paths to @sympro-ui@ files and directories, which are
-- consulted in "Ambient.Profiler.EmbeddedData". Ideally, we'd just put these
-- directly in "Ambient.Profiler.EmbeddedData", but that would trip up GHC
-- staging restrictions.
module Ambient.Profiler.Paths
  ( profilerDir
  , profileHtmlPath
  ) where

import System.FilePath ( (</>) )

profilerDir :: FilePath
profilerDir = "submodules" </> "sympro-ui"

profileHtmlPath :: FilePath
profileHtmlPath = "profile.html"
