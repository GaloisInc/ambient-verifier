module Ambient.Loader.Relocations
  ( RelocType(..)
  ) where

-- | An architecture-independent description of the type of a relocation.
data RelocType
  = CopyReloc
    -- ^ A @COPY@ relocation (e.g., @R_ARM_COPY@). These reference the value of
    -- a global variable in a separate shared library.
  | GlobDatReloc
    -- ^ A @GLOB_DATA@ relocation (e.g., @R_ARM_GLOB_DAT@). These reference the
    -- address of a global variable in a separate shared library.
