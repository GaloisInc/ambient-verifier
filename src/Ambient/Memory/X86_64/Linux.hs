{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# Language ScopedTypeVariables #-}

module Ambient.Memory.X86_64.Linux (
    x86_64LinuxStmtExtensionOverride
  , x86_64LinuxInitGlobals
  ) where

import           Control.Lens ((^.))
import qualified Data.BitVector.Sized as BVS

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.X86 as DMX
import qualified Data.Macaw.X86.Symbolic as DMXS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Common as LCCC
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified What4.Interface as WI
import qualified What4.Symbol as WSym

import qualified Ambient.Memory as AM
import qualified Ambient.Panic as AP

-- | Memory segment size in bytes
segmentSize :: Integer
segmentSize = 4 * 1024

-- | Offset base pointer should point to within a memory segment
segmentBaseOffset :: Integer
segmentBaseOffset = segmentSize `div` 2

-- | Create an initialize a new memory segment
initSegmentMemory :: ( LCB.IsSymBackend sym bak
                     , LCLM.HasLLVMAnn sym
                     , ?memOpts :: LCLM.MemOptions
                     )
                  => bak
                  -> LCLM.MemImpl sym
                  -- ^ MemImpl to add the memory segment to
                  -> String
                  -- ^ Name for the array storage backing the new segment
                  -> IO ( LCLM.LLVMPtr sym (DMC.ArchAddrWidth DMX.X86_64)
                       -- Base pointer for new memory segment
                        , LCLM.MemImpl sym )
                       -- ^ Updated MemImpl containing new memory segment
initSegmentMemory bak mem0 symbol = do
  let sym = LCB.backendGetSym bak
  let ?ptrWidth = WI.knownRepr
  arrayStorage <- WI.freshConstant sym (WSym.safeSymbol symbol) WI.knownRepr
  segmentSizeBV <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr segmentSize)
  oneByte <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr 1)
  (segmentPtr, mem1) <-
    LCLM.doCalloc bak mem0 segmentSizeBV oneByte LCLD.noAlignment
  mem2 <- LCLM.doArrayStore bak
                            mem1
                            segmentPtr
                            LCLD.noAlignment
                            arrayStorage
                            segmentSizeBV

  -- GCC generally appears to place TLS variables at negative offsets from
  -- FSBASE (for an example of this, see the generated 'fsbase.exe' test binary
  -- in 'tests/binaries').  However, online code examples (such as
  -- https://unix.stackexchange.com/questions/453749/what-sets-fs0x28-stack-canary)
  -- also show GCC occasionally placing values at positive offsets from FSBASE.
  -- To support both cases, we put the segment base pointer in the middle of
  -- the allocation.
  segmentBaseOffsetBv <- WI.bvLit sym
                                  WI.knownRepr
                                  (BVS.mkBV WI.knownRepr segmentBaseOffset)
  basePtr <- LCLM.ptrAdd sym WI.knownRepr segmentPtr segmentBaseOffsetBv
  return (basePtr, mem2)

-- | This function takes global variables for the FSBASE and GSBASE pointers
-- and returns an 'InitArchSpecificGlobals' that initializes those globals
-- and inserts them into the global variable state.
x86_64LinuxInitGlobals
  :: ( ?memOpts :: LCLM.MemOptions
     )
  => LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for FSBASE pointer
  -> LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for GSBASE pointer
  -> AM.InitArchSpecificGlobals DMX.X86_64
x86_64LinuxInitGlobals fsbaseGlob gsbaseGlob =
  AM.InitArchSpecificGlobals $ \bak mem0 -> do
    (fsbasePtr, mem1) <- initSegmentMemory bak mem0 "fs_array"
    (gsbasePtr, mem2) <- initSegmentMemory bak mem1 "gs_array"
    let globals0 = LCSG.insertGlobal fsbaseGlob fsbasePtr LCSG.emptyGlobals
    return (mem2, LCSG.insertGlobal gsbaseGlob gsbasePtr globals0)

-- | Return the value in a global variable.  This function panics if the
-- variable doesn't exist.
readGlobal :: LCCC.GlobalVar tp
           -- ^ Global variable to lookup
           -> LCSE.SimState p sym ext rtp g b
           -- ^ State containing the global
           -> LCS.RegValue sym tp
           -- ^ Value in the global
readGlobal global state =
  case LCSG.lookupGlobal global (state ^. LCSE.stateTree . LCSE.actFrame . LCSE.gpGlobals) of
    Nothing -> AP.panic AP.Memory
                        "readGlobal"
                        [ "Failed to find global variable: "
                          ++ show (LCCC.globalName global) ]
    Just ptr -> ptr

-- | Given global variables for the FSBASE and GSBASE pointers, returns a
-- MacawArchStmtExtensionOverride that properly handles reads from FSBASE and
-- GSBASE.
x86_64LinuxStmtExtensionOverride
  :: LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for FSBASE pointer
  -> LCCC.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth DMX.X86_64))
  -- ^ Global variable for GSBASE pointer
  -> DMS.MacawArchStmtExtensionOverride DMX.X86_64
x86_64LinuxStmtExtensionOverride fsbaseGlobal gsbaseGlobal =
  DMS.MacawArchStmtExtensionOverride $ \stmt state -> do
    case stmt of
      DMXS.X86PrimFn fn ->
        case fn of
          DMX.ReadFSBase ->
            return (Just ((readGlobal fsbaseGlobal state), state))
          DMX.ReadGSBase ->
            return (Just ((readGlobal gsbaseGlobal state), state))
          _ -> -- Use default implementation for all other X86PrimFns
            return Nothing
      _ -> -- Use default implementation for all other statement types
        return Nothing
