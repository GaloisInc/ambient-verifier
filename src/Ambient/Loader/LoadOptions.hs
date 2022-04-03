module Ambient.Loader.LoadOptions
  ( indexToLoadOptions
  ) where

import           Data.Word ( Word64 )

import qualified Data.Macaw.Memory.LoadCommon as MML

-- | Given an index value, constructs an 'MML.LoadOptions' for the appropriate
-- offset to load a shared object at.
indexToLoadOptions :: Word64 -> MML.LoadOptions
indexToLoadOptions index =
  -- NOTE: This load offset calculation is safe so long as all binaries are
  -- under 256MB.  It seems likely that something else in the verifier would
  -- fail before binaries reach that size.
  -- NOTE: On 32-bit architectures 'index' values of 16 or higher will cause
  -- the offset to reach inaccessible values.  Macaw throws an exception in
  -- this case.  If this occurs in practice we will need to reduce the offset
  -- multiplier to something smaller (the trade-off is that the maximum
  -- allowable library size will also decrease).
  MML.LoadOptions { MML.loadOffset = Just $ 0x10000000 * index }
