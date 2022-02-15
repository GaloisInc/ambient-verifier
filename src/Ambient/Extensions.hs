{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- | Defines verifier-specific extension evaluation functions.
module Ambient.Extensions
  ( ambientExtensions
  ) where

import           Control.Lens ( (^.) )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Backend as DMSB
import qualified Data.Macaw.Symbolic.MemOps as DMSMO
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE

-- | Return @ambient-verifier@ extension evaluation functions.
ambientExtensions ::
     ( LCB.IsSymInterface sym
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     )
  => DMS.MacawArchEvalFn sym LCLM.Mem arch
  -> LCS.GlobalVar LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem (DMC.ArchAddrWidth arch)
  -> DMS.LookupFunctionHandle sym arch
  -- ^ A function to translate virtual addresses into function handles
  -- dynamically during symbolic execution
  -> DMS.LookupSyscallHandle sym arch
  -- ^ A function to examine the machine state to determine which system call
  -- should be invoked; returns the function handle to invoke
  -> DMS.MkGlobalPointerValidityAssertion sym (DMC.ArchAddrWidth arch)
  -- ^ A function to make memory validity predicates
  -> LCSE.ExtensionImpl (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
ambientExtensions f mvar globs lookupH lookupSyscall toMemPred =
  (DMS.macawExtensions f mvar globs lookupH lookupSyscall toMemPred)
    { LCSE.extensionExec = execAmbientStmtExtension f mvar globs lookupH lookupSyscall toMemPred
    }

-- | This evaluates a Macaw statement extension in the simulator.
execAmbientStmtExtension ::
     ( LCB.IsSymInterface sym
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     )
  => DMS.MacawArchEvalFn sym LCLM.Mem arch
  -> LCS.GlobalVar LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem (DMC.ArchAddrWidth arch)
  -> DMS.LookupFunctionHandle sym arch
  -- ^ A function to turn machine addresses into Crucible function
  -- handles (which can also perform lazy CFG creation)
  -> DMS.LookupSyscallHandle sym arch
  -- ^ A function to examine the machine state to determine which system call
  -- should be invoked; returns the function handle to invoke
  -> DMS.MkGlobalPointerValidityAssertion sym (DMC.ArchAddrWidth arch)
  -- ^ A function to make memory validity predicates
  -> DMSB.MacawEvalStmtFunc (DMS.MacawStmtExtension arch) (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
execAmbientStmtExtension f mvar globs lookupH lookupSyscall toMemPred s0 st =
  LCSE.withBackend (st ^. LCSE.stateContext) $ \bak ->
  let sym = LCB.backendGetSym bak in
  -- NB: Most of this code is copied directly from the 'execMacawStmtExtension'
  -- function in macaw-symbolic.
  case s0 of
    DMS.MacawReadMem addrWidth memRep ptr0 -> do
      mem <- DMSMO.getMem st mvar
      ptr <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerRead
      mGlobalPtrValid <- toMemPred sym puse Nothing ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      (,st) <$> DMSMO.doReadMem bak mem addrWidth memRep ptr
    DMS.MacawCondReadMem addrWidth memRep cond ptr0 condFalseValue -> do
      mem <- DMSMO.getMem st mvar
      ptr <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerRead
      mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      (,st) <$> DMSMO.doCondReadMem bak mem addrWidth memRep (LCS.regValue cond) ptr (LCS.regValue condFalseValue)
    DMS.MacawWriteMem addrWidth memRep ptr0 v -> do
      mem <- DMSMO.getMem st mvar
      ptr <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerWrite
      mGlobalPtrValid <- toMemPred sym puse Nothing ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      mem1 <- DMSMO.doWriteMem bak mem addrWidth memRep ptr (LCS.regValue v)
      pure ((), DMSMO.setMem st mvar mem1)
    DMS.MacawCondWriteMem addrWidth memRep cond ptr0 v -> do
      mem <- DMSMO.getMem st mvar
      ptr <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerWrite
      mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      mem1 <- DMSMO.doCondWriteMem bak mem addrWidth memRep (LCS.regValue cond) ptr (LCS.regValue v)
      pure ((), DMSMO.setMem st mvar mem1)
    _ -> LCSE.extensionExec (DMS.macawExtensions f mvar globs lookupH lookupSyscall toMemPred) s0 st
