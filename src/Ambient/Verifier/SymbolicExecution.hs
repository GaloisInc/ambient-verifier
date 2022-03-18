{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Ambient.Verifier.SymbolicExecution (
    SymbolicExecutionConfig(..)
  , symbolicallyExecute
  , insertFreshGlobals
  , InitialMemory(..)
  , initializeMemory
  , FunctionConfig(..)
  ) where

import           Control.Lens ( Lens', (^.), set, over )
import           Control.Monad ( foldM )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(..) )
import qualified Data.BitVector.Sized as BVS
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as DT
import           GHC.TypeNats ( KnownNat, type (<=) )
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lumberjack as LJ
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
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.Intrinsics as LCLI
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LCLMP
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Simulator.OverrideSim as LCSO
import qualified Lang.Crucible.SymIO as LCSy
import qualified Lang.Crucible.SymIO.Loader as LCSL
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Symbol as WSym
import qualified What4.BaseTypes as WT

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Exception as AE
import qualified Ambient.Extensions as AExt
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.Memory as AM
import qualified Ambient.Panic as AP
import qualified Ambient.Property.Definition as APD
import qualified Ambient.Solver as AS
import qualified Ambient.Syscall as ASy
import qualified Ambient.Verifier.Concretize as AVC
import qualified Ambient.Verifier.WMM as AVW

data SymbolicExecutionConfig arch sym =
  SymbolicExecutionConfig { secProperties :: [APD.Property APD.StateID]
                          , secWMMCallback :: AVW.WMMCallback arch sym
                          , secSolver :: AS.Solver
                          }

-- | The stack size in bytes
stackSize :: Integer
stackSize = 2 * 1024 * 1024

stackOffset :: Integer
stackOffset = stackSize `div` 2

-- | Heap size in bytes
heapSize :: Integer
heapSize = 2 * 1024 * 1024 * 1024

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
lookupFunction :: forall sym bak arch p ext w scope solver st fs args ret mem
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , LCCE.IsSyntaxExtension ext
     , DMS.SymArchConstraints arch
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , p ~ AExt.AmbientSimulatorState arch
     , ext ~ DMS.MacawExt arch
     , w ~ DMC.ArchAddrWidth arch
     , args ~ (LCT.EmptyCtx LCT.::>
               LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
     , ret ~ LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
     , WPO.OnlineSolver solver
     )
   => bak
   -> DMS.GenArchVals mem arch
   -> DMM.Memory w
   -- ^ Memory from function discovery
   -> FunctionConfig w args ret arch sym p ext
   -- ^ Configuration parameters concerning functions and overrides
   -> AF.FunctionABI arch sym p
   -- ^ Function call ABI specification for 'arch'
   -> LCF.HandleAllocator
   -> DMS.LookupFunctionHandle p sym arch
lookupFunction bak archVals discoveryMem fnConf abi hdlAlloc =
  DMS.LookupFunctionHandle $ \state _mem regs -> do
    let regsEntry = LCS.RegEntry regsRepr regs
    -- Extract instruction pointer value and look the address up in
    -- 'addressToFnHandle'
    let offset = LCLMP.llvmPointerOffset $ LCS.regValue
                                         $ DMS.lookupReg archVals regsEntry DMC.ip_reg
    funcAddr <- fromIntegral <$> resolveConcreteStackVal bak (Proxy @arch) AE.FunctionAddress offset
    lookupHandle funcAddr state

  where
    symArchFns :: DMS.MacawSymbolicArchFunctions arch
    symArchFns = DMS.archFunctions archVals

    crucRegTypes :: Ctx.Assignment LCT.TypeRepr (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
    crucRegTypes = DMS.crucArchRegTypes symArchFns

    regsRepr :: LCT.TypeRepr ret
    regsRepr = LCT.StructRepr crucRegTypes

    -- This function abstracts over a common pattern when dealing with lazily
    -- registering overrides (Note [Lazily registering overrides] in A.Extensions):
    --
    -- (1) First, check to see if the function has had an override registered
    --     previously by looking in the appropriate spot in the
    --     AmbientSimulatorState. If so, just use that handle.
    -- (2) If not, check to see if the user supplied an override for this
    --     function by looking in the appropriate spot in the FunctionABI.
    --     If so, register that override, allocate a new handle for it, and
    --     return that handle.
    -- (3) If not, perform some other action.
    lazilyRegisterHandle ::
         forall key rtp blocks r ctx
       . Ord key
      => LCS.CrucibleState p sym ext rtp blocks r ctx
      -> key
         -- ^ The type of function. This can be a MemWord (for kernel-specific
         --   functions) or a FunctionName (for other kinds of functions).
      -> Lens' (AExt.AmbientSimulatorState arch)
               (Map.Map key (AF.FunctionOverrideHandle arch))
         -- ^ A lens into the corresponding field of AmbientSimulatorState.
         --   This is used both in step (1), for checking if the key is
         --   present, and in step (2), for updating the state when
         --   registering the override.
      -> Map.Map key (AF.SomeFunctionOverride p sym ext)
         -- ^ A Map (contained in the FunctionABI) that contains user-supplied
         --   overrides.
      -> IO ( LCF.FnHandle args ret
            , LCS.CrucibleState p sym ext rtp blocks r ctx
            )
         -- The action to perform in step (3).
      -> IO ( LCF.FnHandle args ret
            , LCS.CrucibleState p sym ext rtp blocks r ctx
            )
         -- The function handle to use, as well as the updated state.
    lazilyRegisterHandle state key ovHandlesL fnAbiMap noFnFoundInAbiMap = do
      -- Step (1)
      case Map.lookup key (state ^. LCS.stateContext . LCS.cruciblePersonality . ovHandlesL) of
        Just handle -> pure (handle, state)
        Nothing ->
          -- Step (2)
          case Map.lookup key fnAbiMap of
            Just (AF.SomeFunctionOverride fnOverride) -> do
              (handle, state') <- mkAndBindOverride state fnOverride
              let state'' = over (LCS.stateContext . LCS.cruciblePersonality . ovHandlesL)
                                 (Map.insert key handle)
                                 state'
              pure (handle, state'')
            Nothing -> -- Step (3)
                       noFnFoundInAbiMap

    -- Lookup a function handle from an address.  Performs the lookup in the
    -- following order:
    --
    -- (1) Check for override for 'funcAddr' at a fixed address in kernel
    --     memory.  If not found, proceed to (2).
    -- (2) If 'funcAddr' points to a PLT stub, dispatch an override.  Otherwise
    --     proceed to (3).
    -- (3) Resolve the function name corresponding to 'funcAddr'.  If an
    --     override is registered to that name, dispatch the override.
    --     Otherwise proceed to (4).
    -- (4) Return the function handle found during discovery for 'funcAddr'.
    --
    -- In each of steps (1)–(3), we check at the beginning to see if the
    -- function's handle has been registered previously. If so, we just use
    -- that. We only allocate a new function handle if it has not been
    -- registered before.
    -- See Note [Lazily registering overrides] in A.Extensions.
    lookupHandle
      :: forall rtp blocks r ctx
       . DMME.MemWord w
      -> LCS.CrucibleState p sym ext rtp blocks r ctx
      -> IO ( LCF.FnHandle args ret
            , LCS.CrucibleState p sym ext rtp blocks r ctx
            )
    lookupHandle funcAddr state =
      lazilyRegisterHandle state funcAddr AExt.functionKernelAddrOvHandles
                           (AF.functionKernelAddrMapping abi) $
        case Map.lookup funcAddr (fcPltStubs fnConf) of
          -- If 'funcAddr' points to a PLT stub, dispatch an override.
          -- Otherwise continue resolving the function address.
          Just fnName -> overridePLTStubByName fnName state
          Nothing -> do
            funcAddrOff <- resolveFuncAddr funcAddr
            handle <- lookupFuncAddrOff funcAddrOff
            applyOverrideIfFound handle state

    -- If we have an override for a certain function name, construct a function
    -- handle for that override. Otherwise, return the supplied function handle
    -- unchanged.
    applyOverrideIfFound
      :: forall rtp blocks r ctx
       . LCF.FnHandle args ret
      -> LCS.CrucibleState p sym ext rtp blocks r ctx
      -> IO ( LCF.FnHandle args ret
            , LCS.CrucibleState p sym ext rtp blocks r ctx
            )
    applyOverrideIfFound handle state =
      lazilyRegisterHandle state (LCF.handleName handle) AExt.functionOvHandles
                           (AF.functionNameMapping abi) $
        pure (handle, state)

    overridePLTStubByName
      :: forall rtp blocks r ctx
       . WF.FunctionName
      -> LCS.CrucibleState p sym ext rtp blocks r ctx
      -> IO ( LCF.FnHandle args ret
            , LCS.CrucibleState p sym ext rtp blocks r ctx
            )
    overridePLTStubByName fnName state =
      lazilyRegisterHandle state fnName AExt.functionOvHandles
                           (AF.functionNameMapping abi) $
        case Map.lookup fnName (fcSoSymbolToFnHandle fnConf) of
          Nothing ->
            CMC.throwM (AE.UnhandledPLTStub fnName)
          Just handle -> pure (handle, state)

    resolveFuncAddr :: DMME.MemWord w -> IO (DMME.MemSegmentOff w)
    resolveFuncAddr funcAddr =
      case DMM.resolveRegionOff discoveryMem (fcRegion fnConf) funcAddr of
        Nothing -> panic ["Failed to resolve function address: " ++ show funcAddr]
        Just funcAddrOff -> pure funcAddrOff

    lookupFuncAddrOff :: DMM.MemSegmentOff w -> IO (LCF.FnHandle args ret)
    lookupFuncAddrOff funcAddrOff =
      case Map.lookup funcAddrOff (fcAddressToFnHandle fnConf) of
        -- TODO: Rather than panicking, we should re-run code discovery
        -- to attempt to locate the function (see issue #13)
        Nothing -> panic ["Failed to find function in function handle mapping"]
        Just handle -> pure handle

    mkAndBindOverride :: forall fnArgs fnRet rtp blocks r ctx
                       . LCS.CrucibleState p sym ext rtp blocks r ctx
                      -> AF.FunctionOverride p sym fnArgs ext fnRet
                      -> IO ( LCF.FnHandle args ret
                            , LCS.CrucibleState p sym ext rtp blocks r ctx
                            )
    mkAndBindOverride state fnOverride = do
      -- Construct an override for the function
      let retOV :: forall r'
                 . LCSO.OverrideSim p sym ext r' args ret
                                   (Ctx.Assignment (LCS.RegValue' sym)
                                                   (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
          retOV = do
            argMap <- LCS.getOverrideArgs
            let argReg = massageRegAssignment $ LCS.regMap argMap
            args <- liftIO $
              AF.functionIntegerArgumentRegisters abi bak
                                                  (AF.functionArgTypes fnOverride)
                                                  argReg
            AF.functionIntegerReturnRegisters abi bak
                                              (AF.functionReturnType fnOverride)
                                              (AF.functionOverride fnOverride bak args)
                                              argReg

      let ov :: LCSO.Override p sym ext args ret
          ov = LCSO.mkOverride' (AF.functionName fnOverride) regsRepr retOV

      -- Build a function handle for the override and insert it into the
      -- state
      bindOverrideHandle state hdlAlloc (Ctx.singleton regsRepr) crucRegTypes ov

    -- Massage the RegEntry Assignment that getOverrideArgs provides into the
    -- form that FunctionABI expects.
    massageRegAssignment ::
         Ctx.Assignment (LCS.RegEntry sym) (Ctx.EmptyCtx LCT.::> LCT.StructType ctx)
      -> Ctx.Assignment (LCS.RegValue' sym) ctx
    massageRegAssignment = LCS.unRV . Ctx.last . FC.fmapFC (LCS.RV . LCS.regValue)

    panic :: [String] -> a
    panic = AP.panic AP.SymbolicExecution "lookupFunction"

-- | This function builds a function handle for an override and inserts it into
-- a state's function bindings
bindOverrideHandle :: MonadIO m
                   => LCS.SimState p sym ext r f a
                   -- ^ State to insert function handle into
                   -> LCF.HandleAllocator
                   -> Ctx.Assignment LCT.TypeRepr args
                   -- ^ Types of arguments to override
                   -> LCT.CtxRepr ctx
                   -- ^ Override return type
                   -> LCSO.Override p sym ext args (LCT.StructType ctx)
                   -- ^ Override to build binding for
                   -> m ( LCF.FnHandle args (LCT.StructType ctx)
                       -- New function handle for override
                        , LCS.SimState p sym ext r f a)
                       -- ^ Updated state containing new function handle
bindOverrideHandle state hdlAlloc atps rtps ov = do
  let LCS.FnBindings curHandles = state ^. LCS.stateContext ^. LCS.functionBindings
  handle <- liftIO $ LCF.mkHandle' hdlAlloc
                                   (LCS.overrideName ov)
                                   atps
                                   (LCT.StructRepr rtps)
  let newHandles = LCS.FnBindings $
                   LCF.insertHandleMap handle
                                       (LCS.UseOverride ov)
                                       curHandles
  let state' = set (LCS.stateContext . LCS.functionBindings)
                   newHandles
                   state
  return (handle, state')

-- | This function is used to generate a function handle for an override once a
-- syscall is encountered
lookupSyscall
  :: forall sym bak arch p ext scope solver st fs
   . ( WI.IsExpr (WI.SymExpr sym)
     , LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , DMS.SymArchConstraints arch
     , p ~ AExt.AmbientSimulatorState arch
     , ext ~ DMS.MacawExt arch
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     )
  => bak
  -> ASy.SyscallABI arch sym p
  -- ^ System call ABI specification for 'arch'
  -> LCF.HandleAllocator
  -> DMS.LookupSyscallHandle p sym arch
lookupSyscall bak abi hdlAlloc =
  DMS.LookupSyscallHandle $ \(atps :: LCT.CtxRepr atps) (rtps :: LCT.CtxRepr rtps) state reg -> do
    -- Extract system call number from register state
    syscallReg <- liftIO $ ASy.syscallNumberRegister abi bak atps reg
    let regVal = LCS.regValue syscallReg
    syscallNum <- resolveConcreteStackVal bak (Proxy @arch) AE.SyscallNumber regVal

    -- Look for override associated with system call number, registering it if
    -- it has not already been so.
    lazilyRegisterHandle state atps rtps syscallNum
  where
    -- This function abstracts over a common pattern when dealing with lazily
    -- registering overrides (see Note [Lazily registering overrides] in
    -- A.Extensions):
    --
    -- First, check to see if the syscall has had an override registered
    -- previously by looking in the AmbientSimulatorState. (See
    -- Note [Lazily registering overrides] in A.Extensions.) If so, just use
    -- that handle. If not, apply a user-supplied override for this syscall.
    lazilyRegisterHandle :: forall atps rtps rtp blocks r ctx
                          . LCS.CrucibleState p sym ext rtp blocks r ctx
                         -> LCT.CtxRepr atps
                         -> LCT.CtxRepr rtps
                         -> Integer
                         -> IO ( LCF.FnHandle atps (LCT.StructType rtps)
                               , LCS.CrucibleState p sym ext rtp blocks r ctx
                               )
    lazilyRegisterHandle state atps rtps syscallNum = do
      let syscallNumRepr = ASy.SyscallNumRepr atps rtps syscallNum
      case MapF.lookup syscallNumRepr (state ^. LCS.stateContext . LCS.cruciblePersonality . AExt.syscallOvHandles) of
        Just (ASy.SyscallFnHandle handle) ->
          pure (handle, state)
        Nothing ->
          applyOverride state syscallNumRepr

    -- Apply a user-supplied override for the syscall, throwing an exception if
    -- an override cannot be found.
    applyOverride :: forall atps rtps rtp blocks r ctx
                   . LCS.CrucibleState p sym ext rtp blocks r ctx
                  -> ASy.SyscallNumRepr '(atps, rtps)
                  -> IO ( LCF.FnHandle atps (LCT.StructType rtps)
                        , LCS.CrucibleState p sym ext rtp blocks r ctx
                        )
    applyOverride state syscallNumRepr@(ASy.SyscallNumRepr atps rtps syscallNum) =
      case Map.lookup syscallNum (ASy.syscallMapping abi) of
        Just (ASy.SomeSyscall syscall) -> do
          (handle, state') <- mkAndBindOverride state atps rtps syscall
          let state'' = over (LCS.stateContext . LCS.cruciblePersonality . AExt.syscallOvHandles)
                             (MapF.insert syscallNumRepr (ASy.SyscallFnHandle handle))
                             state'
          pure (handle, state'')
        Nothing -> CMC.throwM $ AE.UnsupportedSyscallNumber syscallNum

    mkAndBindOverride :: forall atps rtps syscallArgs syscallRet rtp blocks r ctx
                       . LCS.CrucibleState p sym ext rtp blocks r ctx
                      -> LCT.CtxRepr atps
                      -> LCT.CtxRepr rtps
                      -> ASy.Syscall p sym syscallArgs ext syscallRet
                      -> IO ( LCF.FnHandle atps (LCT.StructType rtps)
                            , LCS.CrucibleState p sym ext rtp blocks r ctx
                            )
    mkAndBindOverride state atps rtps syscall = do
      -- Construct an override for the system call
      let retOV :: forall r'
                 . LCSO.OverrideSim p sym ext r' atps (LCT.StructType rtps)
                                    (Ctx.Assignment (LCS.RegValue' sym) rtps)
          retOV = do
            argMap <- LCSO.getOverrideArgs
            let argReg = massageRegAssignment $ LCS.regMap argMap
            args <- liftIO $
              ASy.syscallArgumentRegisters abi bak atps argReg
                                           (ASy.syscallArgTypes syscall)
            ASy.syscallReturnRegisters abi (ASy.syscallReturnType syscall)
                                           (ASy.syscallOverride syscall bak args)
                                           atps argReg rtps

      let ov :: LCSO.Override p sym ext atps (LCT.StructType rtps)
          ov = LCSO.mkOverride' (ASy.syscallName syscall)
                                (LCT.StructRepr rtps) retOV

      -- Build a function handle for the override and insert it into the
      -- state
      bindOverrideHandle state hdlAlloc atps rtps ov

    -- Massage the RegEntry Assignment that getOverrideArgs provides into the
    -- form that Syscall expects.
    massageRegAssignment ::
         Ctx.Assignment (LCS.RegEntry sym) ctx
      -> LCS.RegEntry sym (LCT.StructType ctx)
    massageRegAssignment assn =
      LCS.RegEntry (LCT.StructRepr (FC.fmapFC LCS.regType assn))
                   (FC.fmapFC (LCS.RV . LCS.regValue) assn)

-- | Resolve a bitvector value that was spilled to the stack as concrete. This
-- is used for both syscall numbers and function addresses, and it requires
-- some fancy footwork to do successfully.
-- See @Note [Resolving concrete syscall numbers and function addresses]@.
resolveConcreteStackVal ::
     ( LCB.IsSymInterface sym
     , DMS.SymArchConstraints arch
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     )
  => LCBO.OnlineBackend solver scope st fs
  -> proxy arch
  -> AE.ConcretizationTarget
  -> WI.SymBV sym (DMC.ArchAddrWidth arch)
  -> IO Integer
resolveConcreteStackVal bak _ target stackVal = do
  res <- AVC.resolveSymBVAs bak WT.knownNat stackVal
  case res of
    Left AVC.SolverUnknown ->
      CMC.throwM $ AE.ConcretizationFailedUnknown target
    Left AVC.UnsatInitialAssumptions ->
      AP.panic AP.SymbolicExecution "resolverConcreteStackVal"
        ["Initial assumptions are unsatisfiable"]
    Left AVC.MultipleModels ->
      CMC.throwM $ AE.ConcretizationFailedSymbolic target
    Right stackVal' ->
      pure $ BVS.asUnsigned stackVal'

{-
Note [Resolving concrete syscall numbers and function addresses]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Resolving a syscall number as concrete isn't quite as straightforward as
calling `asBV`. This is because we use the SMT array memory model, if we spill
the value of a syscall number to the stack, then it's not directly possible to
resolve that value as concrete. This is because the value consists of reads
from an SMT array concatenated together.

Instead of using `asBV`, we can query the SMT solver directly to figure out if
a syscall number value is concrete or symbolic. To do so, we.

1. Ask the online solver for a model of the system call number (using
   `checkAndGetModel`), and
2. Send a second query that forbids that model. That is, `assume` that
   bvEq <original-syscall-num-value> <modelled-syscall-num-value> is false,
   and then `check`.

If the second step yields `Unsat`, then we have a concrete syscall number. If
the second step yields `Sat`, however, we have a truly symbolic syscall number.
For now, we fail when given truly symbolic syscall numbers.

All of the same reasoning applies to function addresses, which are resolved in
a similar fashion.
-}

-- | Initialize a list of globals to have fresh symbolic values and insert them
-- into global state.
insertFreshGlobals :: forall sym
                    . (LCB.IsSymInterface sym)
                   => sym
                   -> [Some LCS.GlobalVar]
                   -- ^ List of global variables to initialize
                   -> LCSG.SymGlobalState sym
                   -- ^ Global state to insert variables into
                   -> IO (LCSG.SymGlobalState sym)
                   -- ^ Updated global state
insertFreshGlobals sym globs initialState = foldM go initialState globs
  where
    go :: LCSG.SymGlobalState sym
       -> Some LCS.GlobalVar
       -> IO (LCSG.SymGlobalState sym)
    go state (Some glob) = do
      let tp = LCS.globalType glob
      let name = DT.unpack (LCS.globalName glob)
      case LCT.asBaseType tp of
        LCT.NotBaseType ->
          case tp of
            LCLM.LLVMPointerRepr w -> do
              -- Create a pointer with symbolic region and offset
              region <- WI.freshNat sym (WI.safeSymbol (name ++ "-region"))
              offset <- WI.freshConstant sym
                                         (WI.safeSymbol (name ++ "-offset"))
                                         (WI.BaseBVRepr w)
              let ptr = LCLM.LLVMPointer region offset
              return $ LCSG.insertGlobal glob ptr state
            _ -> CMC.throwM (AE.UnsuportedGlobalVariableType name tp)
        LCT.AsBaseType bt -> do
          val <- WI.freshConstant sym (WI.safeSymbol name) bt
          return $ LCSG.insertGlobal glob val state

-- | Initial memory state for symbolic execution
data InitialMemory sym w =
  InitialMemory { imMemVar :: LCS.GlobalVar LCLM.Mem
               -- ^ MemVar to use in simulation
                , imGlobals :: LCSG.SymGlobalState sym
               -- ^ Initial global variables
                , imStackBasePtr :: LCLM.LLVMPtr sym w
               -- ^ Stack memory base pointer
                , imHeapEndGlob :: LCS.GlobalVar (LCLMP.LLVMPointerType w)
               -- ^ Pointer to the end of heap memory
                , imValidityCheck :: DMS.MkGlobalPointerValidityAssertion sym w
               -- ^ Additional pointer validity checks to enforce
                , imGlobalMap :: DMS.GlobalMap sym LCLM.Mem w
               -- ^ Globals used by the macaw translation; note that this is
               -- separate from the global variable map passed to crucible, as
               -- it is only used for initializing the macaw extension
                }

globalMemoryHooks :: DMSM.GlobalMemoryHooks w
globalMemoryHooks = DMSM.GlobalMemoryHooks {
    -- For now, do nothing
    DMSM.populateRelocation = \_ _ -> return []
  }

initializeMemory
  :: forall sym bak arch w p ext m t st fs
   . ( ?memOpts :: LCLM.MemOptions
     , MonadIO m
     , LCB.IsSymBackend sym bak
     , w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , KnownNat w
     , sym ~ WE.ExprBuilder t st fs
     , 1 <= w
     , 16 <= w )
  => bak
  -> LCF.HandleAllocator
  -> DMA.ArchitectureInfo arch
  -> NEL.NonEmpty (DMM.Memory w)
  -> AM.InitArchSpecificGlobals arch
  -- ^ Function to initialize special global variables needed for 'arch'
  -> [ AF.SomeFunctionOverride p sym ext ]
  -- ^ A list of additional function overrides to register.
  -> m ( InitialMemory sym w )
initializeMemory bak halloc archInfo mems (AM.InitArchSpecificGlobals initGlobals) functionOvs = do
  let sym = LCB.backendGetSym bak

  -- Initialize memory
  let endianness = DMSM.toCrucibleEndian (DMA.archEndianness archInfo)
  let ?recordLLVMAnnotation = \_ _ _ -> return ()
  (initMem, memPtrTbl) <- liftIO $ DMSM.newMergedGlobalMemoryWith globalMemoryHooks (Proxy @arch) bak endianness DMSM.ConcreteMutable mems
  let validityCheck = DMSM.mkGlobalPointerValidityPred memPtrTbl
  let globalMap = DMSM.mapRegionPointers memPtrTbl

  -- Allocate memory for the stack, initialize it with symbolic contents, and
  -- then insert it into the memory model
  stackArrayStorage <- liftIO $ WI.freshConstant sym (WSym.safeSymbol "stack_array") WI.knownRepr
  stackSizeBV <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackSize)
  let ?ptrWidth = WI.knownRepr
  (stackBasePtr, mem1) <- liftIO $ LCLM.doMalloc bak LCLM.StackAlloc LCLM.Mutable "stack_alloc" initMem stackSizeBV LCLD.noAlignment
  mem2 <- liftIO $ LCLM.doArrayStore bak mem1 stackBasePtr LCLD.noAlignment stackArrayStorage stackSizeBV

  -- Initialize heap memory
  heapSizeBv <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr heapSize)
  (heapBasePtr, mem3) <- liftIO $ LCLM.doMalloc bak LCLM.HeapAlloc LCLM.Mutable "<malloc bump>" mem2 heapSizeBv LCLD.noAlignment
  heapEndPtr <- liftIO $ LCLM.ptrAdd sym WI.knownRepr heapBasePtr heapSizeBv
  heapEndGlob <- liftIO $ LCCC.freshGlobalVar halloc
                                              (DT.pack "heapFreeEnd")
                                              (LCLM.LLVMPointerRepr WI.knownNat)

  memVar <- liftIO $ LCLM.mkMemVar (DT.pack "ambient-verifier::memory") halloc
  (mem4, globals0) <- liftIO $ initGlobals bak mem3
  let globals1 = LCSG.insertGlobal memVar mem4 $
                 LCSG.insertGlobal heapEndGlob heapEndPtr globals0
  let functionOvGlobals = concat [ AF.functionGlobals ov
                                 | AF.SomeFunctionOverride ov <- functionOvs ]
  globals2 <- liftIO $ insertFreshGlobals sym functionOvGlobals globals1

  return (InitialMemory memVar
                        globals2
                        stackBasePtr
                        heapEndGlob
                        validityCheck
                        globalMap)

-- | Configuration parameters concerning functions and overrides
data FunctionConfig w args ret arch sym p ext = FunctionConfig {
    fcAddressToFnHandle :: Map.Map (DMM.MemSegmentOff w) (LCF.FnHandle args ret)
  -- ^ Mapping from discovered function addresses to function handles
  , fcFnBindings :: LCF.FnHandleMap (LCS.FnState p sym (DMS.MacawExt arch))
  -- ^ Function bindings to insert into the simulation context
  , fcBuildSyscallABI :: ASy.BuildSyscallABI arch sym p
  -- ^ Function to construct an ABI specification for system calls
  , fcBuildFunctionABI :: AF.BuildFunctionABI arch sym p
  -- ^ Function to construct an ABI specification for function calls
  , fcFunctionOverrides :: [ AF.SomeFunctionOverride p sym ext ]
  -- ^ A list of additional function overrides to register
  , fcRegion :: DMM.RegionIndex
  -- ^ The memory region index containing functions
  , fcPltStubs :: Map.Map (DMME.MemWord w) WF.FunctionName
  -- ^ Mapping from PLT stub addresses to function names
  , fcSoSymbolToFnHandle :: Map.Map WF.FunctionName (LCF.FnHandle args ret)
  -- ^ Mapping from symbols in shared objects to function handles
  }

simulateFunction
  :: ( CMC.MonadThrow m
     , MonadIO m
     , ext ~ DMS.MacawExt arch
     , LCCE.IsSyntaxExtension ext
     , LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , DMS.SymArchConstraints arch
     , w ~ DMC.ArchAddrWidth arch
     , 16 <= w
     , ret ~ LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
     , args ~ (LCT.EmptyCtx LCT.::> ret)
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , ?memOpts :: LCLM.MemOptions
     , p ~ AExt.AmbientSimulatorState arch
     )
  => LJ.LogAction IO AD.Diagnostic
  -> bak
  -> [LCS.GenericExecutionFeature sym]
  -> LCF.HandleAllocator
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -> SymbolicExecutionConfig arch sym
  -> InitialMemory sym w
  -> LCCC.CFG (DMS.MacawExt arch) blocks (Ctx.EmptyCtx Ctx.::> DMS.ArchRegStruct arch) (DMS.ArchRegStruct arch)
  -> DMM.Memory w
  -- ^ Memory from function discovery
  -> Maybe FilePath
  -- ^ Path to the symbolic filesystem.  If this is 'Nothing', the file system
  -- will be empty
  -> FunctionConfig w args ret arch sym p ext
  -- ^ Configuration parameters concerning functions and overrides
  -> m ( LCS.GlobalVar LCLM.Mem
       , LCS.ExecResult p sym ext (LCS.RegEntry sym (DMS.ArchRegStruct arch))
       , AVW.WMConfig
       )
simulateFunction logAction bak execFeatures halloc archVals seConf initialMem cfg discoveryMem mFsRoot fnConf = do
  let sym = LCB.backendGetSym bak
  let symArchFns = DMS.archFunctions archVals
  let crucRegTypes = DMS.crucArchRegTypes symArchFns
  let regsRepr = LCT.StructRepr crucRegTypes

  -- Set up an initial register state (mostly symbolic, with an initial stack)
  --
  -- Put the stack pointer in the middle of our allocated stack so that both sides can be addressed
  initialRegs <- liftIO $ DMS.macawAssignToCrucM (mkInitialRegVal symArchFns sym) (DMS.crucGenRegAssignment symArchFns)
  stackInitialOffset <- liftIO $ WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackOffset)
  sp <- liftIO $ LCLM.ptrAdd sym WI.knownRepr (imStackBasePtr initialMem) stackInitialOffset
  let initialRegsEntry = LCS.RegEntry regsRepr initialRegs
  let regsWithStack = DMS.updateReg archVals initialRegsEntry DMC.sp_reg sp

  let arguments = LCS.RegMap (Ctx.singleton regsWithStack)

  -- Initialize the file system
  fileContents <- liftIO $
    case mFsRoot of
      Nothing -> return LCSy.emptyInitialFileSystemContents
      Just fsRoot -> LCSL.loadInitialFiles sym fsRoot
  let ?ptrWidth = WI.knownRepr
  (fs, globals0, LCLS.SomeOverrideSim initFSOverride) <- liftIO $
    LCLS.initialLLVMFileSystem halloc sym WI.knownRepr fileContents [] (imGlobals initialMem)

  (wmConfig, globals1) <- liftIO $ AVW.initWMConfig sym halloc globals0 (secProperties seConf)

  -- FIXME: We might want to add all known functions to the map here. As an
  -- alternative design, we might be able to lazily add functions as they are
  -- encountered in calls
  let simAction = LCS.runOverrideSim regsRepr (initFSOverride >> (LCS.regValue <$> LCS.callCFG cfg arguments))

  DMS.withArchEval archVals sym $ \archEvalFn -> do
    let ASy.BuildSyscallABI buildSyscallABI = fcBuildSyscallABI fnConf
    let syscallABI = buildSyscallABI fs (imMemVar initialMem) (AVW.wmProperties wmConfig)
    let AF.BuildFunctionABI buildFunctionABI = fcBuildFunctionABI fnConf
    let functionABI = buildFunctionABI fs (imHeapEndGlob initialMem) (imMemVar initialMem) (fcFunctionOverrides fnConf) Map.empty
    let extImpl = AExt.ambientExtensions bak archEvalFn (imMemVar initialMem) (imGlobalMap initialMem) (lookupFunction bak archVals discoveryMem fnConf functionABI halloc) (lookupSyscall bak syscallABI halloc) (imValidityCheck initialMem)
    -- Note: the 'Handle' here is the target of any print statements in the
    -- Crucible CFG; we shouldn't have any, but if we did it would be better to
    -- capture the output over a pipe.
    let ctx = LCS.initSimContext bak (MapF.union LCLI.llvmIntrinsicTypes LCLS.llvmSymIOIntrinsicTypes) halloc IO.stdout (LCS.FnBindings (fcFnBindings fnConf)) extImpl AExt.emptyAmbientSimulatorState
    let s0 = LCS.InitialState ctx globals1 LCS.defaultAbortHandler regsRepr simAction

    let wmCallback = secWMMCallback seConf
    let wmSolver = secSolver seConf
    let wmm = AVW.wmmFeature logAction wmSolver archVals wmCallback (AVW.wmProperties wmConfig)
    let executionFeatures = wmm : fmap LCS.genericToExecutionFeature execFeatures

    res <- liftIO $ LCS.executeCrucible executionFeatures s0
    return (imMemVar initialMem, res, wmConfig)

-- | Symbolically execute a function
--
-- Note that this function currently discards the results of symbolic execution
--
-- NOTE: This currently fixes the memory model as 'DMS.LLVMMemory' (i.e., the
-- default memory model for machine code); we will almost certainly need a
-- modified memory model.
symbolicallyExecute
  :: forall m sym bak arch binFmt w blocks args ret solver scope st fs ext p
   . ( CMC.MonadThrow m
     , MonadIO m
     , LCB.IsSymBackend sym bak
     , LCCE.IsSyntaxExtension (DMS.MacawExt arch)
     , ext ~ DMS.MacawExt arch
     , LCCE.IsSyntaxExtension ext
     , DMB.BinaryLoader arch binFmt
     , DMS.SymArchConstraints arch
     , w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , 16 <= w
     , KnownNat w
     , ret ~ LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))
     , args ~ (LCT.EmptyCtx LCT.::> ret)
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , ?memOpts :: LCLM.MemOptions
     , p ~ AExt.AmbientSimulatorState arch
     )
  => LJ.LogAction IO AD.Diagnostic
  -> bak
  -> LCF.HandleAllocator
  -> DMA.ArchitectureInfo arch
  -> DMS.GenArchVals DMS.LLVMMemory arch
  -> SymbolicExecutionConfig arch sym
  -> NEL.NonEmpty (DMB.LoadedBinary arch binFmt)
  -> [LCS.GenericExecutionFeature sym]
  -> LCCC.CFG (DMS.MacawExt arch) blocks (Ctx.EmptyCtx Ctx.::> DMS.ArchRegStruct arch) (DMS.ArchRegStruct arch)
  -> DMM.Memory w
  -- ^ Memory from function discovery
  -> AM.InitArchSpecificGlobals arch
  -- ^ Function to initialize special global variables needed for 'arch'
  -> Maybe FilePath
  -- ^ Path to the symbolic filesystem.  If this is 'Nothing', the file system
  -- will be empty
  -> FunctionConfig w args ret arch sym p ext
  -- ^ Configuration parameters concerning functions and overrides
  -> m ( LCS.GlobalVar LCLM.Mem
       , LCS.ExecResult p sym ext (LCS.RegEntry sym (DMS.ArchRegStruct arch))
       , AVW.WMConfig
       )
symbolicallyExecute logAction bak halloc archInfo archVals seConf loadedBinaries execFeatures cfg discoveryMem initGlobals mFsRoot fnConf = do
  let mems = NEL.map DMB.memoryImage loadedBinaries
  initialMem <- initializeMemory bak
                                 halloc
                                 archInfo
                                 mems
                                 initGlobals
                                 (fcFunctionOverrides fnConf)
  let ?recordLLVMAnnotation = \_ _ _ -> return ()
  simulateFunction logAction bak execFeatures halloc archVals seConf initialMem cfg discoveryMem mFsRoot fnConf
