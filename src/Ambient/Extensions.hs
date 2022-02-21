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
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Backend as DMSB
import qualified Data.Macaw.Symbolic.MemOps as DMSMO
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified What4.Expr as WE
import qualified What4.Protocol.Online as WPO

import qualified Ambient.Verifier.Concretize as AVC

-- | Return @ambient-verifier@ extension evaluation functions.
ambientExtensions ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     )
  => bak
  -> DMS.MacawArchEvalFn (DMS.MacawSimulatorState sym) sym LCLM.Mem arch
  -> LCS.GlobalVar LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem (DMC.ArchAddrWidth arch)
  -> DMS.LookupFunctionHandle (DMS.MacawSimulatorState sym) sym arch
  -- ^ A function to translate virtual addresses into function handles
  -- dynamically during symbolic execution
  -> DMS.LookupSyscallHandle (DMS.MacawSimulatorState sym) sym arch
  -- ^ A function to examine the machine state to determine which system call
  -- should be invoked; returns the function handle to invoke
  -> DMS.MkGlobalPointerValidityAssertion sym (DMC.ArchAddrWidth arch)
  -- ^ A function to make memory validity predicates
  -> LCSE.ExtensionImpl (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
ambientExtensions bak f mvar globs lookupH lookupSyscall toMemPred =
  (DMS.macawExtensions f mvar globs lookupH lookupSyscall toMemPred)
    { LCSE.extensionExec = execAmbientStmtExtension bak f mvar globs lookupH lookupSyscall toMemPred
    }

-- | This evaluates a Macaw statement extension in the simulator.
execAmbientStmtExtension ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     )
  => bak
  -> DMS.MacawArchEvalFn (DMS.MacawSimulatorState sym) sym LCLM.Mem arch
  -> LCS.GlobalVar LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem (DMC.ArchAddrWidth arch)
  -> DMS.LookupFunctionHandle (DMS.MacawSimulatorState sym) sym arch
  -- ^ A function to turn machine addresses into Crucible function
  -- handles (which can also perform lazy CFG creation)
  -> DMS.LookupSyscallHandle (DMS.MacawSimulatorState sym) sym arch
  -- ^ A function to examine the machine state to determine which system call
  -- should be invoked; returns the function handle to invoke
  -> DMS.MkGlobalPointerValidityAssertion sym (DMC.ArchAddrWidth arch)
  -- ^ A function to make memory validity predicates
  -> DMSB.MacawEvalStmtFunc (DMS.MacawStmtExtension arch) (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch)
execAmbientStmtExtension bak f mvar globs lookupH lookupSyscall toMemPred s0 st =
  let sym = LCB.backendGetSym bak in
  -- NB: Most of this code is copied directly from the 'execMacawStmtExtension'
  -- function in macaw-symbolic. One notable difference is the use of
  -- 'AVC.resolveSingletonPointer' to attempt to concrete the pointer being
  -- read from—or, the pointer being written to—in cases relating to
  -- reading or writing memory, respectively.
  case s0 of
    DMS.MacawReadMem addrWidth memRep ptr0 -> DMM.addrWidthClass addrWidth $ do
      mem <- DMSMO.getMem st mvar
      ptr1 <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      ptr2 <- AVC.resolveSingletonPointer bak ptr1
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerRead
      mGlobalPtrValid <- toMemPred sym puse Nothing ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      (,st) <$> DMSMO.doReadMem bak mem addrWidth memRep ptr2
    DMS.MacawCondReadMem addrWidth memRep cond ptr0 condFalseValue -> DMM.addrWidthClass addrWidth $ do
      mem <- DMSMO.getMem st mvar
      ptr1 <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      ptr2 <- AVC.resolveSingletonPointer bak ptr1
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerRead
      mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      (,st) <$> DMSMO.doCondReadMem bak mem addrWidth memRep (LCS.regValue cond) ptr2 (LCS.regValue condFalseValue)
    DMS.MacawWriteMem addrWidth memRep ptr0 v -> DMM.addrWidthClass addrWidth $ do
      mem <- DMSMO.getMem st mvar
      ptr1 <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      ptr2 <- AVC.resolveSingletonPointer bak ptr1
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerWrite
      mGlobalPtrValid <- toMemPred sym puse Nothing ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      mem1 <- DMSMO.doWriteMem bak mem addrWidth memRep ptr2 (LCS.regValue v)
      pure ((), DMSMO.setMem st mvar mem1)
    DMS.MacawCondWriteMem addrWidth memRep cond ptr0 v -> DMM.addrWidthClass addrWidth $ do
      mem <- DMSMO.getMem st mvar
      ptr1 <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      ptr2 <- AVC.resolveSingletonPointer bak ptr1
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerWrite
      mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      mem1 <- DMSMO.doCondWriteMem bak mem addrWidth memRep (LCS.regValue cond) ptr2 (LCS.regValue v)
      pure ((), DMSMO.setMem st mvar mem1)
    _ -> LCSE.extensionExec (DMS.macawExtensions f mvar globs lookupH lookupSyscall toMemPred) s0 st
