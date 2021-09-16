{-# LANGUAGE RankNTypes #-}

module Ambient.Memory (
    InitArchSpecificGlobals(..)
  ) where

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator.GlobalState as LCSG

-- | 'InitArchSpecificGlobals' provides a function signature for initialization
-- of global variables that are only present on certain architectures or
-- operating systems (e.g., FSBASE on x86).
newtype InitArchSpecificGlobals arch =
  InitArchSpecificGlobals (  forall sym
                             .  ( LCLM.HasLLVMAnn sym
                                , LCB.IsSymInterface sym )
                             => sym
                             -> LCLM.MemImpl sym
                             -- ^ MemImpl to update
                             -> IO ( LCLM.MemImpl sym
                                  -- ^ Updated MemImpl
                                   , LCSG.SymGlobalState sym) )
                                  -- ^ Global state containing architecture
                                  -- specific globals
