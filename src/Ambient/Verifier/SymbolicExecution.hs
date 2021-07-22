{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Ambient.Verifier.SymbolicExecution (
  symbolicallyExecute
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(..) )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as DT
import           GHC.TypeNats ( KnownNat, type (<=) )
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified System.IO as IO

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.ElfLoader as DMME
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Memory as DMSM
import qualified Data.Macaw.Types as DMT
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.Intrinsics as LCLI
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI
import qualified What4.Symbol as WSym
import qualified What4.BaseTypes as WT

import qualified Ambient.Panic as AP

-- | Convert from macaw endianness to the LLVM memory model endianness
toCrucibleEndian :: DMME.Endianness -> LCLD.EndianForm
toCrucibleEndian e =
  case e of
    DMME.LittleEndian -> LCLD.LittleEndian
    DMME.BigEndian -> LCLD.BigEndian

-- | The stack size in bytes
stackSize :: Integer
stackSize = 2 * 1024 * 1024

stackOffset :: Integer
stackOffset = stackSize `div` 2

mkInitialRegVal
  :: (LCB.IsSymInterface sym, DMT.HasRepr (DMC.ArchReg arch) DMT.TypeRepr)
  => DMS.MacawSymbolicArchFunctions arch
  -> sym
  -> DMC.ArchReg arch tp
  -> IO (LCS.RegValue' sym (DMS.ToCrucibleType tp))
mkInitialRegVal symArchFns sym r = do
  let regName = DMS.crucGenArchRegName symArchFns r
  case DMT.typeRepr r of
    DMT.BoolTypeRepr ->
      LCS.RV <$> WI.freshConstant sym regName WT.BaseBoolRepr
    DMT.BVTypeRepr w -> do
      c <- WI.freshConstant sym regName (WT.BaseBVRepr w)
      LCS.RV <$> LCLM.llvmPointer_bv sym c
    DMT.TupleTypeRepr PL.Nil -> return (LCS.RV Ctx.Empty)
    DMT.TupleTypeRepr _ ->
      AP.panic AP.SymbolicExecution "mkInitialRegVal" ["Tuple-typed registers are not supported in initial states: " ++ show regName]
    DMT.FloatTypeRepr {} ->
      AP.panic AP.SymbolicExecution "mkInitialRegVal" ["Float-typed registers are not supported in initial states: " ++ show regName]
    DMT.VecTypeRepr {} ->
      AP.panic AP.SymbolicExecution "mkInitialRegVal" ["Vector-typed registers are not supported in initial states: " ++ show regName]

-- | This function is used to look up a function handle when a call is encountered
--
-- NOTE: This currently only works for concrete function addresses, but once
-- https://github.com/GaloisInc/crucible/pull/615 lands, we should update it to
-- return a mux of all possible targets.
lookupFunction :: forall sym arch w args ret
   . ( LCB.IsSymInterface sym
     , LCCE.IsSyntaxExtension (DMS.MacawExt arch)
     , DMS.SymArchConstraints arch
     , w ~ DMC.ArchAddrWidth arch
     , args ~ (LCT.EmptyCtx LCT.::>
               LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
     , ret ~ LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
   => DMS.GenArchVals DMS.LLVMMemory arch
   -> DMM.Memory w
   -- ^ Memory from function discovery
   -> Map.Map (DMM.MemSegmentOff w) (LCF.FnHandle args ret)
   -- ^ Mapping from function addresses to function handles
   -> DMS.LookupFunctionHandle sym arch
lookupFunction archVals discoveryMem addressToFnHandle = DMS.LookupFunctionHandle $ \s _mem regs -> do
  let symArchFns = DMS.archFunctions archVals
  let crucRegTypes = DMS.crucArchRegTypes symArchFns
  let regsRepr = LCT.StructRepr crucRegTypes
  let regsEntry = LCS.RegEntry regsRepr regs
  -- Extract instruction pointer value and look the address up in
  -- 'addressToFnHandle'
  case LCS.regValue (DMS.lookupReg archVals regsEntry DMC.ip_reg) of
    LCLM.LLVMPointer _ offset ->
      case BVS.asUnsigned <$> WI.asBV offset of
        Nothing -> AP.panic AP.SymbolicExecution
                            "lookupFunction"
                            ["Attempted to call function with non-concrete address"]
        Just funcAddr ->
          case DMM.resolveRegionOff discoveryMem 0 (fromIntegral funcAddr) of
            Nothing -> AP.panic AP.SymbolicExecution
                                "lookupFunction"
                                ["Failed to resolve function address"]
            Just funcAddrOff ->
              case Map.lookup funcAddrOff addressToFnHandle of
                -- TODO: Rather than panicking, we should re-run code discovery
                -- to attempt to locate the function (see issue #13)
                Nothing -> AP.panic AP.SymbolicExecution
                                    "lookupFunction"
                                    ["Failed to find function in function handle mapping"]
                Just handle -> return (handle, s)

simulateFunction
  :: ( CMC.MonadThrow m
     , MonadIO m
     , ext ~ DMS.MacawExt arch
     , LCCE.IsSyntaxExtension ext
     , LCB.IsSymInterface sym
     , LCLM.HasLLVMAnn sym
     , DMS.SymArchConstraints arch
     , w ~ DMC.ArchAddrWidth arch
     , 16 <= w
     , ret ~ LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
     , args ~ (LCT.EmptyCtx LCT.::> ret)
     )
  => sym
  -> [LCS.GenericExecutionFeature sym]
  -> LCF.HandleAllocator
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -> LCLM.MemImpl sym
  -> DMS.GlobalMap sym LCLM.Mem w
  -- ^ Globals used by the macaw translation; note that this is separate from
  -- the global variable map passed to crucible, as it is only used for
  -- initializing the macaw extension
  -> LCCC.CFG (DMS.MacawExt arch) blocks (Ctx.EmptyCtx Ctx.::> DMS.ArchRegStruct arch) (DMS.ArchRegStruct arch)
  -> DMS.MkGlobalPointerValidityAssertion sym w
  -- ^ Additional pointer validity checks to enforce
  -> DMM.Memory w
  -- ^ Memory from function discovery
  -> Map.Map (DMM.MemSegmentOff w) (LCF.FnHandle args ret)
  -- ^ Mapping from discovered function addresses to function handles
  -> LCF.FnHandleMap (LCS.FnState (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch))
  -- ^ Function bindings to insert into the simulation context
  -> m ( LCS.GlobalVar LCLM.Mem
       , LCS.ExecResult (DMS.MacawSimulatorState sym) sym ext (LCS.RegEntry sym (DMS.ArchRegStruct arch))
       )
simulateFunction sym execFeatures halloc archVals initMem globalMap cfg validityCheck discoveryMem addressToFnHandle fnBindings = do
  let symArchFns = DMS.archFunctions archVals
  let crucRegTypes = DMS.crucArchRegTypes symArchFns
  let regsRepr = LCT.StructRepr crucRegTypes

  -- Initialize memory

  -- Allocate memory for the stack, initialize it with symbolic contents, and
  -- then insert it into the memory model
  stackArrayStorage <- liftIO $ WI.freshConstant sym (WSym.safeSymbol "stack_array") WI.knownRepr
  stackSizeBV <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackSize)
  let ?ptrWidth = WI.knownRepr
  (stackBasePtr, mem1) <- liftIO $ LCLM.doMalloc sym LCLM.StackAlloc LCLM.Mutable "stack_alloc" initMem stackSizeBV LCLD.noAlignment
  mem2 <- liftIO $ LCLM.doArrayStore sym mem1 stackBasePtr LCLD.noAlignment stackArrayStorage stackSizeBV

  -- Set up an initial register state (mostly symbolic, with an initial stack)
  --
  -- Put the stack pointer in the middle of our allocated stack so that both sides can be addressed
  initialRegs <- liftIO $ DMS.macawAssignToCrucM (mkInitialRegVal symArchFns sym) (DMS.crucGenRegAssignment symArchFns)
  stackInitialOffset <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackOffset)
  sp <- liftIO $ LCLM.ptrAdd sym WI.knownRepr stackBasePtr stackInitialOffset
  let initialRegsEntry = LCS.RegEntry regsRepr initialRegs
  let regsWithStack = DMS.updateReg archVals initialRegsEntry DMC.sp_reg sp

  memVar <- liftIO $ LCLM.mkMemVar (DT.pack "ambient-verifier::memory") halloc
  let initGlobals = LCSG.insertGlobal memVar mem2 LCS.emptyGlobals
  let arguments = LCS.RegMap (Ctx.singleton regsWithStack)
  -- FIXME: We might want to add all known functions to the map here. As an
  -- alternative design, we might be able to lazily add functions as they are
  -- encountered in calls
  let simAction = LCS.runOverrideSim regsRepr (LCS.regValue <$> LCS.callCFG cfg arguments)

  DMS.withArchEval archVals sym $ \archEvalFn -> do
    let extImpl = DMS.macawExtensions archEvalFn memVar globalMap (lookupFunction archVals discoveryMem addressToFnHandle) validityCheck
    -- Note: the 'Handle' here is the target of any print statements in the
    -- Crucible CFG; we shouldn't have any, but if we did it would be better to
    -- capture the output over a pipe.
    let ctx = LCS.initSimContext sym LCLI.llvmIntrinsicTypes halloc IO.stdout (LCS.FnBindings fnBindings) extImpl DMS.MacawSimulatorState
    let s0 = LCS.InitialState ctx initGlobals LCS.defaultAbortHandler regsRepr simAction
    res <- liftIO $ LCS.executeCrucible (fmap LCS.genericToExecutionFeature execFeatures) s0
    return (memVar, res)

-- | Symbolically execute a function
--
-- Note that this function currently discards the results of symbolic execution
--
-- NOTE: This currently fixes the memory model as 'DMS.LLVMMemory' (i.e., the
-- default memory model for machine code); we will almost certainly need a
-- modified memory model.
symbolicallyExecute
  :: forall m sym arch binFmt w blocks args ret
   . ( CMC.MonadThrow m
     , MonadIO m
     , LCB.IsSymInterface sym
     , LCCE.IsSyntaxExtension (DMS.MacawExt arch)
     , DMB.BinaryLoader arch binFmt
     , DMS.SymArchConstraints arch
     , w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , 16 <= w
     , KnownNat w
     , ret ~ LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
     , args ~ (LCT.EmptyCtx LCT.::> ret)
     )
  => sym
  -> LCF.HandleAllocator
  -> DMA.ArchitectureInfo arch
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -> DMB.LoadedBinary arch binFmt
  -> [LCS.GenericExecutionFeature sym]
  -> LCCC.CFG (DMS.MacawExt arch) blocks (Ctx.EmptyCtx Ctx.::> DMS.ArchRegStruct arch) (DMS.ArchRegStruct arch)
  -> DMM.Memory w
  -- ^ Memory from function discovery
  -> Map.Map (DMM.MemSegmentOff w) (LCF.FnHandle args ret)
  -- ^ Mapping from discovered function addresses to function handles
  -> LCF.FnHandleMap (LCS.FnState (DMS.MacawSimulatorState sym) sym (DMS.MacawExt arch))
  -- ^ Function bindings to insert into the simulation context
  -> m ()
symbolicallyExecute sym halloc archInfo archVals loadedBinary execFeatures cfg discoveryMem addressToFnHandle fnBindings = do
  let mem = DMB.memoryImage loadedBinary
  let endianness = toCrucibleEndian (DMA.archEndianness archInfo)
  let ?recordLLVMAnnotation = \_ _ -> return ()
  (initMem, memPtrTbl) <- liftIO $ DMSM.newGlobalMemory (Proxy @arch) sym endianness DMSM.ConcreteMutable mem
  let validityCheck = DMSM.mkGlobalPointerValidityPred memPtrTbl
  let globalMap = DMSM.mapRegionPointers memPtrTbl
  (_memVar, _execResult) <- simulateFunction sym execFeatures halloc archVals initMem globalMap cfg validityCheck discoveryMem addressToFnHandle fnBindings
  return ()
