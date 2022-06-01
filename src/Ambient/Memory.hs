{-# LANGUAGE RankNTypes #-}

module Ambient.Memory (
    InitArchSpecificGlobals(..)
  , InitialMemory(..)
  ) where

import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.GlobalState as LCSG

import qualified Ambient.Extensions.Memory as AEM

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

-- | Initial memory state for symbolic execution
data InitialMemory sym w =
  InitialMemory { imMemVar :: LCS.GlobalVar LCLM.Mem
               -- ^ MemVar to use in simulation
                , imGlobals :: LCSG.SymGlobalState sym
               -- ^ Initial global variables
                , imStackBasePtr :: LCLM.LLVMPtr sym w
               -- ^ Stack memory base pointer
                , imValidityCheck :: DMS.MkGlobalPointerValidityAssertion sym w
               -- ^ Additional pointer validity checks to enforce
                , imGlobalMap :: DMS.GlobalMap sym LCLM.Mem w
               -- ^ Globals used by the macaw translation; note that this is
               -- separate from the global variable map passed to crucible, as
               -- it is only used for initializing the macaw extension
                , imMemPtrTable :: AEM.MemPtrTable sym w
               -- ^ The global memory
                }

