{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Defines verifier-specific extensions for Macaw's simulation functionality.
module Ambient.Extensions
  ( ambientExtensions
  , AmbientSimulatorState(..)
  , incrementSimStat
  , lensNumOvsApplied
  , AmbientSimulationStats(..)
  , emptyAmbientSimulatorState
  , functionOvHandles
  , functionKernelAddrOvHandles
  , syscallOvHandles
  , discoveredFunctionHandles
  , serverSocketFDs
  , simulationStats
  , overrideLookupFunctionHandle
  ) where

import           Control.Lens ( Lens', (^.), lens, (&), (+~))
import qualified Control.Exception as X
import qualified Data.Aeson as DA
import qualified Data.BitVector.Sized as BV
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe, isNothing )
import qualified Data.Parameterized.Map as MapF
import           GHC.Generics ( Generic )

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
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Ambient.Exception as AE
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.Syscall as ASy
import qualified Ambient.Verifier.Concretize as AVC

-- | Return @ambient-verifier@ extension evaluation functions.
ambientExtensions ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     )
  => bak
  -> DMS.MacawArchEvalFn (AmbientSimulatorState sym arch) sym LCLM.Mem arch
  -> LCS.GlobalVar LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem w
  -> DMS.LookupFunctionHandle (AmbientSimulatorState sym arch) sym arch
  -- ^ A function to translate virtual addresses into function handles
  -- dynamically during symbolic execution
  -> DMS.LookupSyscallHandle (AmbientSimulatorState sym arch) sym arch
  -- ^ A function to examine the machine state to determine which system call
  -- should be invoked; returns the function handle to invoke
  -> DMS.MkGlobalPointerValidityAssertion sym w
  -- ^ A function to make memory validity predicates
  -> Map.Map (DMM.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> LCSE.ExtensionImpl (AmbientSimulatorState sym arch) sym (DMS.MacawExt arch)
ambientExtensions bak f mvar globs lookupH lookupSyscall toMemPred unsupportedRelocs =
  (DMS.macawExtensions f mvar globs lookupH lookupSyscall toMemPred)
    { LCSE.extensionExec = execAmbientStmtExtension bak f mvar globs lookupH lookupSyscall toMemPred unsupportedRelocs
    }

-- | This evaluates a Macaw statement extension in the simulator.
execAmbientStmtExtension :: forall sym scope st fs bak solver arch p w.
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , LCLM.HasLLVMAnn sym
     , p ~ AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     , ?memOpts :: LCLM.MemOptions
     , DMM.MemWidth w
     )
  => bak
  -> DMS.MacawArchEvalFn p sym LCLM.Mem arch
  -> LCS.GlobalVar LCLM.Mem
  -> DMS.GlobalMap sym LCLM.Mem w
  -> DMS.LookupFunctionHandle p sym arch
  -- ^ A function to turn machine addresses into Crucible function
  -- handles (which can also perform lazy CFG creation)
  -> DMS.LookupSyscallHandle p sym arch
  -- ^ A function to examine the machine state to determine which system call
  -- should be invoked; returns the function handle to invoke
  -> DMS.MkGlobalPointerValidityAssertion sym w
  -- ^ A function to make memory validity predicates
  -> Map.Map (DMM.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> DMSB.MacawEvalStmtFunc (DMS.MacawStmtExtension arch) p sym (DMS.MacawExt arch)
execAmbientStmtExtension bak f mvar globs lookupH lookupSyscall toMemPred unsupportedRelocs s0 st =
  -- NB: Most of this code is copied directly from the 'execMacawStmtExtension'
  -- function in macaw-symbolic. One notable difference is the use of
  -- 'AVC.resolveSingletonPointer' to attempt to concrete the pointer being
  -- read from—or, the pointer being written to—in cases relating to
  -- reading or writing memory, respectively.
  case s0 of
    DMS.MacawReadMem addrWidth memRep ptr0 -> DMM.addrWidthClass addrWidth $ do
      mem <- DMSMO.getMem st mvar
      ptr1 <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      (ptr2, resolveEffect) <- AVC.resolveSingletonPointer bak ptr1
      assertRelocSupported ptr2
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerRead
      mGlobalPtrValid <- toMemPred sym puse Nothing ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      readVal <- DMSMO.doReadMem bak mem addrWidth memRep ptr2
      let st' = updateReads readVal memRep (updateBoundsRefined resolveEffect st)
      return (readVal,st')
    DMS.MacawCondReadMem addrWidth memRep cond ptr0 condFalseValue -> DMM.addrWidthClass addrWidth $ do
      mem <- DMSMO.getMem st mvar
      ptr1 <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      (ptr2, resolveEffect) <- AVC.resolveSingletonPointer bak ptr1
      assertRelocSupported ptr2
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerRead
      mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      readVal <- DMSMO.doCondReadMem bak mem addrWidth memRep (LCS.regValue cond) ptr2 (LCS.regValue condFalseValue)
      let st' = updateReads readVal memRep (updateBoundsRefined resolveEffect st)
      return (readVal,st')
    DMS.MacawWriteMem addrWidth memRep ptr0 v -> DMM.addrWidthClass addrWidth $ do
      mem <- DMSMO.getMem st mvar
      ptr1 <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      (ptr2, resolveEffect) <- AVC.resolveSingletonPointer bak ptr1
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerWrite
      mGlobalPtrValid <- toMemPred sym puse Nothing ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      mem1 <- DMSMO.doWriteMem bak mem addrWidth memRep ptr2 (LCS.regValue v)
      let st' = updateBoundsRefined resolveEffect st
      pure ((), DMSMO.setMem st' mvar mem1)
    DMS.MacawCondWriteMem addrWidth memRep cond ptr0 v -> DMM.addrWidthClass addrWidth $ do
      mem <- DMSMO.getMem st mvar
      ptr1 <- DMSMO.tryGlobPtr bak mem globs (LCS.regValue ptr0)
      (ptr2, resolveEffect) <- AVC.resolveSingletonPointer bak ptr1
      let puse = DMS.PointerUse (st ^. LCSE.stateLocation) DMS.PointerWrite
      mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> LCB.addAssertion bak globalPtrValid
        Nothing -> return ()
      mem1 <- DMSMO.doCondWriteMem bak mem addrWidth memRep (LCS.regValue cond) ptr2 (LCS.regValue v)
      let st' = updateBoundsRefined resolveEffect st
      pure ((), DMSMO.setMem st' mvar mem1)
    _ ->
      let lookupFnH = fromMaybe lookupH ( st
                                       ^. LCS.stateContext
                                        . LCS.cruciblePersonality
                                        . overrideLookupFunctionHandle ) in
      LCSE.extensionExec (DMS.macawExtensions f mvar globs lookupFnH lookupSyscall toMemPred) s0 st
  where
    sym = LCB.backendGetSym bak

    -- Update the metric tracking the number of symbolic bitvector bounds
    -- refined
    updateBoundsRefined :: AVC.ResolveSymBVEffect
                        -- ^ Effect resolving SymBV had on underlying bitvector
                        -> LCS.CrucibleState p sym ext rtp blocks r ctx
                        -- ^ State to update
                        -> LCS.CrucibleState p sym ext rtp blocks r ctx
    updateBoundsRefined resolveEffect state =
      case resolveEffect of
        AVC.Concretized -> state
        AVC.UnchangedBounds -> state
        AVC.RefinedBounds -> incrementSimStat lensNumBoundsRefined state

    -- Update the metrics tracking the total number of reads and number of
    -- symbolic reads
    updateReads :: LCS.RegValue sym (DMS.ToCrucibleType ty)
                -- ^ Value returned by a read
                -> DMC.MemRepr ty
                -- ^ Type of the read value
                -> LCS.CrucibleState p sym ext rtp blocks r ctx
                -- ^ State to update
                -> LCS.CrucibleState p sym ext rtp blocks r ctx
    updateReads readVal memRep state =
      let state' = incrementSimStat lensNumReads state in
      if readIsSymbolic memRep readVal
      then incrementSimStat lensNumSymbolicReads state'
      else state'

    -- Returns True iff the memory read is at least partly symbolic
    readIsSymbolic :: DMC.MemRepr ty
                   -> LCS.RegValue sym (DMS.ToCrucibleType ty)
                   -> Bool
    readIsSymbolic memRep readVal =
      case memRep of
        DMC.BVMemRepr{} ->
          -- Check whether value is symbolic
          let (LCLM.LLVMPointer base bv) = readVal in
          isNothing (WI.asNat base) || isNothing (WI.asBV bv)
        DMC.FloatMemRepr{} -> isNothing (WI.asConcrete readVal)
        DMC.PackedVecMemRepr _w vecMemRep ->
          -- Recursively look for symbolic values in vector
          any (readIsSymbolic vecMemRep) readVal

    -- | Check whether a pointer points to a relocation address, and if so,
    -- assert that the underlying relocation type is supported.  If not, throw
    -- an UnsupportedRelocation exception.  This is a best effort attempt: if
    -- the read is symbolic the check is skipped.
    assertRelocSupported :: LCLM.LLVMPtr sym w -> IO ()
    assertRelocSupported (LCLM.LLVMPointer _base offset) =
      case WI.asBV offset of
        Nothing ->
          -- Symbolic read.  Cannot check whether this is an unsupported
          -- relocation.
          return ()
        Just bv -> do
          -- Check whether this read is from an unsupported relocation type.
          let addr = DMM.memWord (fromIntegral (BV.asUnsigned bv))
          case Map.lookup addr unsupportedRelocs of
            Just relTypeName ->
              X.throwIO $ AE.UnsupportedRelocation relTypeName
            Nothing -> return ()

-- | Statistics gathered during simulation
data AmbientSimulationStats = AmbientSimulationStats
  { numOvsApplied :: Integer
  -- ^ The total number of times overrides were applied during symbolic
  -- execution
  , numReads :: Integer
  -- ^ Total number of memory reads during simulation
  , numBoundsRefined :: Integer
  -- ^ Total number of symbolic bitvector bounds refined
  , numSymbolicReads :: Integer
  -- ^ Total number of memory reads that are at least partly symbolic
  }
  deriving ( Generic )
instance DA.ToJSON AmbientSimulationStats

emptyAmbientSimulationStats :: AmbientSimulationStats
emptyAmbientSimulationStats =
  AmbientSimulationStats { numOvsApplied = 0
                         , numReads = 0
                         , numBoundsRefined = 0
                         , numSymbolicReads = 0
                         }

-- | Increment a counter in the 'AmbientSimulationStats' held in a given
-- crucible state.
incrementSimStat :: ( p ~ AmbientSimulatorState sym arch )
                 => Lens' AmbientSimulationStats Integer
                 -- ^ Accessor for the stat to update
                 -> LCS.CrucibleState p sym ext rtp blocks r ctx
                 -- ^ State holding the 'AmbientSimulationStats' to update
                 -> LCS.CrucibleState p sym ext rtp blocks r ctx
incrementSimStat statLens state =
  state & LCS.stateContext
        . LCS.cruciblePersonality
        . simulationStats
        . statLens +~ 1

lensNumOvsApplied :: Lens' AmbientSimulationStats Integer
lensNumOvsApplied = lens numOvsApplied (\s v -> s { numOvsApplied = v })

lensNumReads :: Lens' AmbientSimulationStats Integer
lensNumReads = lens numReads (\s v -> s { numReads = v })

lensNumBoundsRefined :: Lens' AmbientSimulationStats Integer
lensNumBoundsRefined = lens numBoundsRefined (\s v -> s { numBoundsRefined = v })

lensNumSymbolicReads :: Lens' AmbientSimulationStats Integer
lensNumSymbolicReads = lens numSymbolicReads (\s v -> s { numSymbolicReads = v })

-- | The state extension for Crucible holding verifier-specific state.
data AmbientSimulatorState sym arch = AmbientSimulatorState
  { _functionOvHandles :: Map.Map WF.FunctionName (AF.FunctionOverrideHandle arch)
    -- ^ A map from registered function overrides to their handles.
    -- See @Note [Lazily registering overrides]@.
  , _functionKernelAddrOvHandles :: Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch)) (AF.FunctionOverrideHandle arch)
    -- ^ A map from registered kernel-specific function overrides to their handles.
    -- See @Note [Lazily registering overrides]@.
  , _syscallOvHandles :: MapF.MapF ASy.SyscallNumRepr ASy.SyscallFnHandle
    -- ^ A map from registered syscall overrides to their handles.
    -- See @Note [Lazily registering overrides]@.
  , _discoveredFunctionHandles :: Map.Map (DMC.ArchSegmentOff arch) (AF.FunctionOverrideHandle arch)
    -- ^ A map of discovered functions to their handles.
    -- See @Note [Incremental code discovery]@.
    --
    -- Note that this puts every address from all binaries' address spaces into
    -- a single map. This happens to work today since we ensure that the
    -- address spaces in each binary are disjoint from each other (see
    -- @Note [Address offsets for shared libraries]@ in
    -- "Ambient.Loader.LoadOffset" for the details). However, we will want to
    -- support more flexible memory layouts such as ASLR in the future. In
    -- those sorts of layouts, we would run the risk of addresses from
    -- different address spaces being mapped to the same 'DMC.ArchSegmentOff',
    -- which will make a 'Map.Map' insufficient means of storage. See #86.
  , _serverSocketFDs :: Map.Map Integer AF.ServerSocketInfo
    -- ^ A map from registered socket file descriptors to their corresponding
    -- metadata. See @Note [The networking story]@ in
    -- "Ambient.FunctionOverride.Overrides".
  , _simulationStats :: AmbientSimulationStats
    -- ^ Metrics from the Ambient simulator
  , _overrideLookupFunctionHandle :: Maybe (DMSMO.LookupFunctionHandle (AmbientSimulatorState sym arch) sym arch)
    -- ^ Override for the default 'DMSMO.LookupFunctionHandle' implementation
    -- in Ambient.Verifier.SymbolicExecution.  If set this will be used for
    -- resolving function calls instead of the default lookup function.
    -- The Weird Machine Executor uses this to replace the default function
    -- lookup with one that will disassemble the function address and use a
    -- more relaxed code discovery classifier to handle gadgets that may
    -- unbalance the stack (which prevents Macaw from detecting them properly).
  }

-- | An initial value for 'AmbientSimulatorState'.
emptyAmbientSimulatorState :: AmbientSimulatorState sym arch
emptyAmbientSimulatorState = AmbientSimulatorState
  { _functionOvHandles = Map.empty
  , _functionKernelAddrOvHandles = Map.empty
  , _syscallOvHandles = MapF.empty
  , _discoveredFunctionHandles = Map.empty
  , _serverSocketFDs = Map.empty
  , _simulationStats = emptyAmbientSimulationStats
  , _overrideLookupFunctionHandle = Nothing
  }

functionOvHandles :: Lens' (AmbientSimulatorState sym arch)
                           (Map.Map WF.FunctionName (AF.FunctionOverrideHandle arch))
functionOvHandles = lens _functionOvHandles
                         (\s v -> s { _functionOvHandles = v })

functionKernelAddrOvHandles :: Lens' (AmbientSimulatorState sym arch)
                                     (Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch)) (AF.FunctionOverrideHandle arch))
functionKernelAddrOvHandles = lens _functionKernelAddrOvHandles
                                   (\s v -> s { _functionKernelAddrOvHandles = v })

syscallOvHandles :: Lens' (AmbientSimulatorState sym arch)
                          (MapF.MapF ASy.SyscallNumRepr ASy.SyscallFnHandle)
syscallOvHandles = lens _syscallOvHandles
                        (\s v -> s { _syscallOvHandles = v })

discoveredFunctionHandles :: Lens' (AmbientSimulatorState sym arch)
                                   (Map.Map (DMC.ArchSegmentOff arch) (AF.FunctionOverrideHandle arch))
discoveredFunctionHandles = lens _discoveredFunctionHandles
                                 (\s v -> s { _discoveredFunctionHandles = v })

serverSocketFDs :: Lens' (AmbientSimulatorState sym arch)
                       (Map.Map Integer AF.ServerSocketInfo)
serverSocketFDs = lens _serverSocketFDs
                       (\s v -> s { _serverSocketFDs = v })

simulationStats :: Lens' (AmbientSimulatorState sym arch) AmbientSimulationStats
simulationStats = lens _simulationStats (\s v -> s { _simulationStats = v })

overrideLookupFunctionHandle
  :: Lens' (AmbientSimulatorState sym arch)
           (Maybe (DMSMO.LookupFunctionHandle (AmbientSimulatorState sym arch) sym arch))
overrideLookupFunctionHandle =
  lens _overrideLookupFunctionHandle
       (\s v -> s { _overrideLookupFunctionHandle = v })

{-
Note [Lazily registering overrides]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
During symbolic simulation, the verifier needs to register function handles for
any overrides that have not yet been used by the simulator. This is done in a
lazy fashion: before the verifier simulates a function, it will check to see
if it has previously registered. If so, just use the previously registered
function handle. If not, allocate a fresh handle for that function, register
it, then proceed. This lazy behavior is helpful for two reasons:

1. In general, the verifier may not have discovered all of the functions it
   needs prior to starting simulation. As a result, at least some lazy
   registration will be required to handle functions that aren't discovered
   until subsequent runs of the code discoverer.

2. As a practical matter, it is difficult to ascertain the types of syscall
   function handles until simulation begins. Lazy registration avoids this
   issue, as one can wait until one is in the context of LookupSyscallHandle,
   where the types are within reach.

We track registered overrides in AmbientSimulatorState, which is a custom
personality data type the verifier tracks during simulation. The
LookupFunctionHandle and LookupSyscallHandle interfaces pass through
CrucibleState, so if we need to register a newly discovered override, it is a
matter of updating the AmbientSimulatorState inside of the CrucibleState and
returning the new state.

Registered overrides for functions can be stored in a simple Map, as their
types are easy to ascertain ahead of time. Registered overrides for syscalls,
on the other hand, are stored in a MapF. Since their types are difficult to
know ahead of time (point (2) above), existentially closing over their types
avoids this problem.

Note [Incremental code discovery]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The verifier will not perform code discovery unless it needs to, as:

1. Code discovery is fairly expensive, and
2. In large binaries, one typically only needs to discover a portion of the
   functions available in the binary.

Because of this, the verifier will only discover one function at a time, and
only if the verifier needs to find an address that has not previously been
discovered before. This has a number of consequences for the design of the
verifier:

* Because code discovery requires knowing which address to discover, the
  first thing the verifier must do is determine the address corresponding
  to the distinguished entry point function so that its code can be discovered.
  If the user manually specifies an address, this is no issue. If the user
  tries to find a function with a particular name, such as `main` (see
  Note [Entry Point] in A.Verifier), then this is somewhat more challenging,
  since we do not know a priori where `main`'s address is. We could uncover
  this information by performing code discovery on all functions in the binary,
  but this would be prohibitively expensive.

  Our solution is to look at the section headers of the binary, which offer a
  much cheaper way to map each function name to its address. This information
  is stored in A.Loader.BinaryConfig.bcMainBinarySymbolMap. Note that this
  won't work if the binary is stripped, but that is to be expected—there is
  no hope of discovering code in a stripped binary unless you know the exact
  address at which to start.

* When looking up a function in the verifier, we want to avoid code discovery
  if the function has a user-supplied override, as the override obviates the
  need to discover the function's CFG. But overrides apply to function names,
  whereas the verifier looks up functions by their addresses. In order to know
  which function addresses have overrides, we need to look up the names for
  each address. This mapping is contained in a LoadedBinaryPath's
  lbpEntryPoints field. Again, this information is gleaned by inspecting each
  binary's section headers.

* When the verifier encounters a PLT stub, it knows the name of the function it
  should jump to. But how does it know which binary the function is defined in?
  We solve this problem by, once again, looking at each binary's section
  headers. In particular, the A.Loader.BinaryConfig.bcDynamicFuncSymbolMap
  field maps the names of global, dynamic functions (which are the only
  functions that PLT stubs could reasonably jump to) to their addresses. When
  the verifier encounters a PLT stub without an override, it will use the
  bcDynamicFuncSymbolMap to determine the address in another binary to jump
  to and then proceed like normal.

* After a function has been discovered for the first time, its CFG handle is
  stored in the discoveredFunctionHandles field of AmbientSimulatorState. That
  way, subsequent lookups of the function need not re-perform code discovery.
  This is very much in the same vein as Note [Lazily registering overrides].
-}
