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
--
-- It takes an initial 'LCMC.MemImpl' and modifies it as necessary, also
-- returning any auxiliary global variables to support the changes.
newtype InitArchSpecificGlobals arch =
  InitArchSpecificGlobals (  forall sym bak
                             .  ( LCLM.HasLLVMAnn sym
                                , LCB.IsSymBackend sym bak )
                             => bak
                             -> LCLM.MemImpl sym
                             -> IO ( LCLM.MemImpl sym
                                   , LCSG.SymGlobalState sym) )
