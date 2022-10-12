{-# LANGUAGE TemplateHaskell #-}

module Ambient.ODSL.EmbeddedData
  ( odslCrucibleHeaderDataFile
  ) where

import Data.ByteString ( ByteString )
import Data.FileEmbed ( embedFile )
import System.FilePath ( (</>) )

import Ambient.ODSL.Paths ( odslIncludesDir, odslCrucibleHeaderPath )

-- | The contents of @overrides-dsl@'s @crucible.h@, which is needed to run a
-- preprocessor on a C override. This is kept in its own module to minimize the
-- costs of recompilation due to Template Haskell file dependency tracking.
odslCrucibleHeaderDataFile :: ByteString
odslCrucibleHeaderDataFile = $(embedFile $ odslIncludesDir </> odslCrucibleHeaderPath)
