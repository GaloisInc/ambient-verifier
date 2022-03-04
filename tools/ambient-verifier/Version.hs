-- | Code taken from the @saw-script@ repo, which is licensed under the
-- 3-Clause BSD license.
module Version
  ( hashText
  , versionText
  , shortVersionText
  ) where

import Paths_ambient_verifier (version)
import GitRev (hash)
import Data.Version (showVersion)

hashText :: String
hashText = " (" ++ hash ++ ")"

versionText :: String
versionText = "version " ++ shortVersionText

shortVersionText :: String
shortVersionText = showVersion version ++ hashText
