{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Defines function overrides that are shared across different architectures.
module Ambient.FunctionOverride.Overrides
  ( -- * crucible-llvm–based overrides
    buildMallocOverride
  , callMalloc
  , buildCallocOverride
  , callCalloc
  , buildMemcpyOverride
  , callMemcpy
  , buildMemsetOverride
  , callMemset
  , buildShmgetOverride
  , callShmget
  , shmatOverride
  , callShmat
    -- * Networking-related overrides
  , networkOverrides
  , buildAcceptOverride
  , callAccept
  , buildBindOverride
  , callBind
  , buildListenOverride
  , callListen
  , buildRecvOverride
  , callRecv
  , buildSendOverride
  , callSend
  , buildSocketOverride
  , callSocket
    -- * Hacky overrides
  , buildHackyBumpMallocOverride
  , hackyBumpMalloc
  , buildHackyBumpCallocOverride
  , hackyBumpCalloc
  ) where

import           Control.Lens ( (%=), (.=), (+=), use )
import qualified Control.Lens as Lens
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString.Char8 as BS
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Text as T
import qualified System.FilePath as FP

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.Bytes as LCLB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.SymIO as LCSy
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Ambient.Exception as AE
import qualified Ambient.Extensions as AExt
import           Ambient.FunctionOverride
import qualified Ambient.Memory.SharedMemory as AMS
import           Ambient.Override
import qualified Ambient.Panic as AP
import qualified Ambient.Syscall.Overrides as ASO
import qualified Ambient.Verifier.Concretize as AVC

-------------------------------------------------------------------------------
-- crucible-llvm–based overrides
-------------------------------------------------------------------------------

buildCallocOverride :: ( LCLM.HasLLVMAnn sym
                       , ?memOpts :: LCLM.MemOptions
                       , LCLM.HasPtrWidth w
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildCallocOverride mvar = FunctionOverride
  { functionName = "calloc"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callCalloc bak mvar) args
  }

callCalloc :: ( LCB.IsSymBackend sym bak
              , LCLM.HasLLVMAnn sym
              , ?memOpts :: LCLM.MemOptions
              , LCLM.HasPtrWidth w
              )
           => bak
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -- ^ The number of elements in the array
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callCalloc bak mvar (LCS.regValue -> num) (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do numBV <- LCLM.projectLLVM_bv bak num
     szBV  <- LCLM.projectLLVM_bv bak sz
     LCLM.doCalloc bak mem szBV numBV LCLD.noAlignment

buildMallocOverride :: ( ?memOpts :: LCLM.MemOptions
                       , LCLM.HasLLVMAnn sym
                       , LCLM.HasPtrWidth w
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildMallocOverride mvar = FunctionOverride
  { functionName = "malloc"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callMalloc bak mvar) args
  }

callMalloc :: ( LCB.IsSymBackend sym bak
              , ?memOpts :: LCLM.MemOptions
              , LCLM.HasLLVMAnn sym
              , LCLM.HasPtrWidth w
              )
           => bak
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callMalloc bak mvar (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let displayString = "<malloc function override>"
     szBV <- LCLM.projectLLVM_bv bak sz
     LCLM.doMalloc bak LCLM.HeapAlloc LCLM.Mutable displayString mem szBV LCLD.noAlignment

buildMemcpyOverride :: ( LCLM.HasPtrWidth w
                       , LCLM.HasLLVMAnn sym
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              LCT.UnitType
buildMemcpyOverride mvar = FunctionOverride
  { functionName = "memcpy"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callMemcpy bak mvar) args
  }

-- | Override for the @memcpy@ function. This behaves identically to the
-- corresponding override in @crucible-llvm@.
callMemcpy :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              , LCLM.HasLLVMAnn sym
              )
           => bak
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim p sym ext r args ret ()
callMemcpy bak mvar (LCS.regValue -> dest) (LCS.regValue -> src) (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do szBV <- LCLM.projectLLVM_bv bak sz
     let ?memOpts = overrideMemOptions
     mem' <- LCLM.doMemcpy bak (LCLM.ptrWidth sz) mem True dest src szBV
     pure ((), mem')

buildMemsetOverride :: ( LCLM.HasPtrWidth w
                       , LCLM.HasLLVMAnn sym
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              LCT.UnitType
buildMemsetOverride mvar = FunctionOverride
  { functionName = "memset"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callMemset bak mvar) args
  }

-- | Override for the @memset@ function. This behaves identically to the
-- corresponding override in @crucible-llvm@.
callMemset :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              , LCLM.HasLLVMAnn sym
              )
           => bak
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim p sym ext r args ret ()
callMemset bak mvar (LCS.regValue -> dest) val (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let w = LCLM.ptrWidth sz
     valBV <- ptrToBv8 bak w val
     szBV <- LCLM.projectLLVM_bv bak sz
     mem' <- LCLM.doMemset bak w mem dest (LCS.regValue valBV) szBV
     pure ((), mem')

-- | Override for the @shmat@ function.  This override only supports calls
-- where @shmaddr@ is @NULL@.  That is, it doesn't support calls where the
-- caller specifies which address the shared memory segment should be mapped
-- to.  This override also ignores the @shmflg@ argument and always maps the
-- memory as read/write.
callShmat :: forall sym scope st fs w solver arch m p ext r args ret
           . ( sym ~ WE.ExprBuilder scope st fs
             , LCB.IsSymInterface sym
             , LCLM.HasPtrWidth w
             , LCLM.HasLLVMAnn sym
             , WPO.OnlineSolver solver
             , p ~ AExt.AmbientSimulatorState sym arch
             , w ~ DMC.ArchAddrWidth arch
             , m ~ LCS.OverrideSim p sym ext r args ret
             )
          => LCBO.OnlineBackend solver scope st fs
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -> m (LCS.RegValue sym (LCLM.LLVMPointerType w))
callShmat bak shmid shmaddr _shmflg = do
  let sym = LCB.backendGetSym bak

  -- Check that shmaddr is NULL.
  nullCond <- liftIO $ LCLM.ptrIsNull sym ?ptrWidth (LCS.regValue shmaddr)
  liftIO $ LCB.assert bak nullCond (LCS.AssertFailureSimError
                                   "Call to shmat() with non-null shmaddr"
                                   "")

  -- Extract ID and lookup in shared memory state
  (shmIdSymBv, resolveEffect) <- liftIO $
        LCLM.projectLLVM_bv bak (LCS.regValue shmid)
    >>= AVC.resolveSymBV bak ?ptrWidth
  updateBoundsRefined resolveEffect
  shmIdBv <- maybe (CMC.throwM AE.SymbolicSharedMemorySegmentId)
                   pure
                   (WI.asBV shmIdSymBv)

  shmState <- use (LCS.stateContext . LCS.cruciblePersonality . AExt.sharedMemoryState)
  let lookupId = AMS.SharedMemoryId $ BVS.asUnsigned shmIdBv
  case AMS.sharedMemorySegmentAt lookupId shmState of
    Nothing -> liftIO $ LCB.addFailedAssertion bak $
       LCS.AssertFailureSimError ("Nonexistent shared memory ID: " ++ show lookupId)
                                 ""
    Just segment -> pure segment
  where
    -- Update the metric tracking the number of symbolic bitvector bounds
    -- refined
    updateBoundsRefined :: AVC.ResolveSymBVEffect -> m ()
    updateBoundsRefined resolveEffect =
      case resolveEffect of
        AVC.Concretized -> pure ()
        AVC.UnchangedBounds -> pure ()
        AVC.RefinedBounds ->
            LCS.stateContext
          . LCS.cruciblePersonality
          . AExt.simulationStats
          . AExt.lensNumBoundsRefined += 1



shmatOverride :: ( LCLM.HasLLVMAnn sym
                 , LCLM.HasPtrWidth w
                 , p ~ AExt.AmbientSimulatorState sym arch
                 , w ~ DMC.ArchAddrWidth arch
                 )
              => FunctionOverride p
                                  sym
                                  (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                Ctx.::> LCLM.LLVMPointerType w
                                                Ctx.::> LCLM.LLVMPointerType w)
                                  ext
                                  (LCLM.LLVMPointerType w)
shmatOverride = FunctionOverride {
    functionName = "shmat"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
                                Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
                                Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callShmat bak) args
  }

-- | Override for the @shmget@ function.  It has the following caveats that may
-- need to be addressed in the future for a more faithful override:
--
-- * @key@ must be @IPC_PRIVATE@.
-- * @size@ is not rounded to a multiple of @PAGE_SIZE@ like it is in the real
--   implementation.
-- * @shmflag@ is ignored.  This is because:
--   * @key == IPC_PRIVATE@ implies that a shared memory segment is being
--     created regardless of whether the @IPC_CREAT@ flag is set.
--   * @key == IPC_PRIVATE@ always satisfies @IPC_EXCL@.
--   * @SHM_NORESERVE@ is irrelevant because we don't model swap space.
--   * The remaining flags concern page sizes and rounding modes, but this
--     override does not faithfully model the rounding behavior of @shmget@
-- * The shared memory IDs that this function returns start at 1 and increment
--   by 1 at each call.  This may differ from the real method of allocating
--   shared memory IDs.
callShmget :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              , LCLM.HasLLVMAnn sym
              , p ~ AExt.AmbientSimulatorState sym arch
              , w ~ DMC.ArchAddrWidth arch
              )
           => LCS.GlobalVar LCLM.Mem
           -> bak
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callShmget mvar bak key size _shmflag = do
  let ?memOpts = overrideMemOptions
  let sym = LCB.backendGetSym bak

  -- Extract and check that key is zero
  keyBv <- liftIO $ LCLM.projectLLVM_bv bak (LCS.regValue key)
  cond <- liftIO $ WI.bvEq sym keyBv =<< WI.bvLit sym ?ptrWidth (BVS.zero ?ptrWidth)
  liftIO $ LCB.assert bak cond (LCS.AssertFailureSimError
                                "Call to shmget() with non-zero key"
                                "")

  -- Allocate shared memory segment
  sizeBv <- liftIO $ LCLM.projectLLVM_bv bak (LCS.regValue size)
  let displayString = "<shared memory segment>"
  LCS.modifyGlobal mvar $ \mem -> do
    (segment, mem') <- liftIO $ LCLM.doMalloc bak
                                              LCLM.HeapAlloc
                                              LCLM.Mutable
                                              displayString
                                              mem
                                              sizeBv
                                              LCLD.noAlignment

    -- Store segment in the shared memory state and get an ID
    shmState <- use (LCS.stateContext . LCS.cruciblePersonality . AExt.sharedMemoryState)
    let (AMS.SharedMemoryId shmId, shmState') =
          AMS.newSharedMemorySegment segment shmState
    LCS.stateContext . LCS.cruciblePersonality . AExt.sharedMemoryState .= shmState'

    -- Convert ID to a BV
    shmIdBv <- liftIO $ WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth shmId)
    shmIdPtr <- liftIO $ LCLM.llvmPointer_bv sym shmIdBv
    return (shmIdPtr, mem')

buildShmgetOverride :: ( LCLM.HasLLVMAnn sym
                       , LCLM.HasPtrWidth w
                       , p ~ AExt.AmbientSimulatorState sym arch
                       , w ~ DMC.ArchAddrWidth arch
                       )
                  => LCS.GlobalVar LCLM.Mem
                  -> FunctionOverride p
                                      sym
                                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                    Ctx.::> LCLM.LLVMPointerType w
                                                    Ctx.::> LCLM.LLVMPointerType w)
                                      ext
                                      (LCLM.LLVMPointerType w)
buildShmgetOverride memVar = FunctionOverride {
    functionName = "shmget"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
                                 Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
                                 Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride =
      \bak args -> Ctx.uncurryAssignment (callShmget memVar bak) args
  }

-------------------------------------------------------------------------------
-- Networking overrides
-------------------------------------------------------------------------------

{-
Note [The networking story]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
The verifier has limited support for socket I/O. The verifier defines enough
overrides (see `networkOverrides`) to simulate basic socket server and client
programs. These overrides emulate socket connections by opening specific files
on the symbolic filesystem.

When a program invokes socket(domain, type, protocol), the following file will
be opened:

  /network/<domain_macro>/<type_macro>/socket

Where:

* <domain_macro> is the name of the C macro that corresponds to the `domain`
  value passed to socket(). For example, a `domain` value of 2 corresponds to
  the AF_INET macro, so that would result in /network/AF_INET/...

* <type_macro> is the name of the C macro that corresponds to the `type` value
  passed to socket(). For example, a `type` value of 1 corresponds to the
  SOCK_STREAM macro, so that would reult in /network/.../SOCK_STREAM/...

For servers, the contents of this .../socket file don't matter that much. For
clients, this file is used for network communication, so
`read`ing/`recv`ing from this file simulates receiving a message from the
server, and `send`ing/`write`ing to this file simulates sending a message to
the server.

When a program invokes accept(sockfd, addr, addrlen), the following file will
be opened:

  /network/<domain_macro>/<type_macro>/<port>/<seq_num>

Where:

* <domain_macro> and <type_macro> are the same values as in the socket() case.
  <port> is the same value that was passed to bind() when assigning a name to
  the socket. (We'll describe how the verifier looks up these values in a bit.)

* <seq_num> indicates the order in which each call to accept() was made. For
  example, the first accept() call will be given a <seq_num> of 0, the second
  accept() call will be given a <seq_num> of 1, etc.

These overrides use a crucible-symio LLVMFileSystem under the hood to track
these files. One limitation of an LLVMFileSystem is that there isn't a simple
way to associate extra metadata with each file. That is to say, after socket()
returns a file descriptor, there isn't an easy way to use that file descriptor
to look up its file path, port number, the number of connections etc. One might
be tempted to pass around a GlobalVar containing this metadata, but it's not
obvious what CrucibleType such a GlobalVar would have, since we would need some
kind of map-like structure.

Our solution to this problem is to add a `serverSocketFDs` field to the
AmbientSimulatorState, which is passed around across all overrides. This
contains a map of file descriptors to ServerSocketInfo, which is a collection of
metadata that gradually gets filled in after calls to socket() and bind().
This is not a perfect solution (more on this in a bit), but it is sufficient to
handle the kinds of network programs we are targeting.

Note that this metadata is only needed in service of figuring out the name of
the filepath that accept() opens, which is only needed for servers. Clients do
not need to invoke accept(), which is why there is not a corresponding
ClientSocketInfo data type.

There are a variety of limitations surrounding how this works to be aware of:

* AmbientSimulatorState is passed around in the `personality` of each
  OverrideSim, which does not participate in branching and merging. One could
  imagine a program for which this is problematic (e.g., a socket that
  conditionally gets created depeneding on the value of symbolic data), but we
  do not anticipate this being an issue in practice.

* Because the names of crucible-symio filepaths must be concrete, a socket's
  domain, type, and port number must all be concrete, since they all appear in
  filepath names. Again, we do not anticipate many programs in the wild will
  try to make this information symbolic. The file descriptor for each socket
  must also be concrete, but since crucible-symio always allocates concrete
  file descriptors anyway, this requirement is easily satisfied.

* The domain value passed to socket() must be listed in the `socketDomainMap`.
  We could, in theory, support other forms of communication, but we do not do so
  at present.

* The type value passed to socket() must be listed in the `socketTypeMap`.
  We could, in theory, support other forms of communication semantics, but we
  do not do so at present.

* Because crucible-symio's open() implementation does not support creating new
  files (see https://github.com/GaloisInc/crucible/issues/803), all of the
  files under the /network directory must be specified ahead of time in the
  initial symbolic filesystem.

* The accept() override, unlike the function it models, completely ignores the
  addr and addrlen arguments. To model accept() more faithfully, it should fill
  in these arguments with information about the peer socket address. See #77.
-}

-- | All of the socket I/O–related overrides, packaged up for your
-- convenience.
networkOverrides :: ( LCLM.HasLLVMAnn sym
                    , LCLM.HasPtrWidth w
                    , w ~ DMC.ArchAddrWidth arch
                    )
                 => LCLS.LLVMFileSystem w
                 -> LCS.GlobalVar LCLM.Mem
                 -> [SomeFunctionOverride (AExt.AmbientSimulatorState sym arch) sym ext]
networkOverrides fs memVar =
  [ SomeFunctionOverride (buildAcceptOverride fs)
  , SomeFunctionOverride (buildBindOverride fs memVar)
  , SomeFunctionOverride buildConnectOverride
  , SomeFunctionOverride buildListenOverride
  , SomeFunctionOverride (buildRecvOverride fs memVar)
  , SomeFunctionOverride (buildSendOverride fs memVar)
  , SomeFunctionOverride (buildSocketOverride fs)
  ]

buildAcceptOverride :: ( LCLM.HasPtrWidth w
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => LCLS.LLVMFileSystem w
                    -> FunctionOverride (AExt.AmbientSimulatorState sym arch) sym
                                        (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                      Ctx.::> LCLM.LLVMPointerType w
                                                      Ctx.::> LCLM.LLVMPointerType w) ext
                                        (LCLM.LLVMPointerType w)
buildAcceptOverride fs = FunctionOverride
  { functionName = "accept"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callAccept fs bak) args
  }

-- | Override for the @accept@ function. This function looks up the metadata
-- associated with the socket file descriptor argument, allocates a new socket
-- file with a unique name, and records this information in the
-- 'AE.AmbientSimulatorState'. See Note @[The networking story]@ for the full
-- details.
callAccept :: ( LCB.IsSymBackend sym bak
              , sym ~ WE.ExprBuilder scope st fs
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , WPO.OnlineSolver solver
              , LCLM.HasPtrWidth w
              , w ~ DMC.ArchAddrWidth arch
              )
           => LCLS.LLVMFileSystem w
           -> bak
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                              (LCS.RegValue sym (LCLM.LLVMPointerType w))
callAccept fs bak sockfd _addr _addrlen = do
  let sym = LCB.backendGetSym bak
  sockfdInt <- liftIO $ networkConstantBVPtrToInteger bak "accept" AE.FDArgument (LCS.regValue sockfd)
  serverSocketFDs <- Lens.use (LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs)
  case Map.lookup sockfdInt serverSocketFDs of
    Just (ServerSocketInfo { serverSocketPort = Just sockPort
                           , serverSocketFilePath = sockFilePath
                           , serverSocketNextConnection = sockNextConn
                           }) -> do
      let connectionFilePath = FP.takeDirectory sockFilePath FP.</>
                               show sockPort FP.</> show sockNextConn
      connectionFileLit <- liftIO $ WI.stringLit sym $ WI.Char8Literal $ BS.pack connectionFilePath
      fd <- LCSy.openFile (LCLS.llvmFileSystem fs) connectionFileLit $ \res -> do
        case res of
          Left LCSy.FileNotFound -> returnIOError
          Right fileHandle -> do
            LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs %=
              Map.adjust (\ssi -> ssi{serverSocketNextConnection = sockNextConn + 1})
                         sockfdInt
            LCLS.allocateFileDescriptor fs fileHandle
      liftIO $ bvToPtr sym fd ?ptrWidth
    _ -> do
      ec <- returnIOError
      liftIO $ bvToPtr sym ec ?ptrWidth

buildBindOverride :: ( LCLM.HasPtrWidth w
                     , LCLM.HasLLVMAnn sym
                     , w ~ DMC.ArchAddrWidth arch
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> FunctionOverride (AExt.AmbientSimulatorState sym arch) sym
                                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                    Ctx.::> LCLM.LLVMPointerType w
                                                    Ctx.::> LCLM.LLVMPointerType w) ext
                                      (LCLM.LLVMPointerType w)
buildBindOverride fs memVar = FunctionOverride
  { functionName = "bind"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callBind fs memVar bak) args
  }

-- | Override for the @bind@ function. This function reads the port number from
-- the @addr@ struct, ensures that it is concrete, and records it for later
-- calls to @accept()@. See Note @[The networking story]@ for the full details.
callBind :: ( LCB.IsSymBackend sym bak
            , sym ~ WE.ExprBuilder scope st fs
            , bak ~ LCBO.OnlineBackend solver scope st fs
            , WPO.OnlineSolver solver
            , LCLM.HasLLVMAnn sym
            , LCLM.HasPtrWidth w
            , w ~ DMC.ArchAddrWidth arch
            )
         => LCLS.LLVMFileSystem w
         -> LCS.GlobalVar LCLM.Mem
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                            (LCS.RegValue sym (LCLM.LLVMPointerType w))
callBind _fs memVar bak sockfd addr _addrlen = do
  let sym = LCB.backendGetSym bak
  sockfdInt <- liftIO $ networkConstantBVPtrToInteger bak "bind" AE.FDArgument (LCS.regValue sockfd)
  serverSocketFDs <- Lens.use (LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs)
  if Map.member sockfdInt serverSocketFDs
    then do mem <- LCS.readGlobal memVar
            portBV <- liftIO $ loadSockaddrInPort bak mem (LCS.regValue addr)
            portInt <- liftIO $ fmap BVS.asUnsigned
                              $ networkConstantBV bak "bind" AE.PortArgument (WI.knownNat @16) portBV
            LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs %=
              Map.adjust (\ssi -> ssi{ serverSocketPort = Just (fromInteger portInt) })
                         sockfdInt
            ec <- returnIOSuccess
            liftIO $ bvToPtr sym ec ?ptrWidth
    else do ec <- returnIOError
            liftIO $ bvToPtr sym ec ?ptrWidth

-- | This function digs through the memory in a pointer to a @sockaddr_in@
-- struct (for @AF_INET@ connections) or a @sockaddr_in6@ struct (for
-- @AF_INET6@ connections) and loads the port number out of it, which is the
-- only information that we care about in the verifier. Note that the port
-- number's bytes will be represented in network order, not host order, so you
-- may want to byteswap it for debugging purposes.
loadSockaddrInPort ::
     ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , LCLM.HasPtrWidth w
     )
  => bak
  -> LCLM.MemImpl sym
  -> LCLM.LLVMPtr sym w
  -> IO (WI.SymBV sym 16)
loadSockaddrInPort bak mem sockaddrInPtr = do
  let sym = LCB.backendGetSym bak
  let -- The size of the @sa_family_t@ type in bytes. While
      -- https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/sys_socket.h.html
      -- requires @sa_family_t@ to be an unsigned integer, it does not specify
      -- what size it should have. As a result, the size could potentially be
      -- different across different OS/architecture configurations.
      --
      -- Fortunately, @sa_family_t@ is two bytes in all of the configurations
      -- that the verifier currently supports, so we have opted to hard-code
      -- this information for the time being. We should eventually move towards
      -- a design that avoids this hard-coding—see #75.
      saFamilyTLenBytes = BVS.mkBV ?ptrWidth 2
  bvSaFamilyTLenBytes <- WI.bvLit sym ?ptrWidth saFamilyTLenBytes
  let ?memOpts = overrideMemOptions
  -- At what offset into the struct should we load to get the port number?
  -- Here are the definitions of @sockaddr_in@ and @sockaddr_in6@,
  -- respectively, for reference:
  --
  -- @
  -- struct sockaddr_in {
  --     sa_family_t    sin_family;
  --     in_port_t      sin_port;
  --     struct in_addr sin_addr;
  -- };
  --
  -- struct sockaddr_in6 {
  --     sa_family_t     sin6_family;
  --     in_port_t       sin6_port;
  --     uint32_t        sin6_flowinfo;
  --     struct in6_addr sin6_addr;
  --     uint32_t        sin6_scope_id;
  -- };
  -- @
  --
  -- Conveniently, the field of type @in_port_t@ is always the second field,
  -- and it always follows a field of type @sa_family_t@. Therefore, we use the
  -- size of @sa_family_t@ to compute the offset.
  sockaddrInPortPtr <- LCLM.doPtrAddOffset bak mem sockaddrInPtr bvSaFamilyTLenBytes
  let -- The size of the @in_port_t@ type in bits. The size of this type
      -- appears to be standardized across all implementations. See, e.g.,.
      -- https://pubs.opengroup.org/onlinepubs/009695399/basedefs/netinet/in.h.html,
      -- which says that @in_port_t@ should always be equivalent to @uint16_t@.
      inPortTLenBits = WI.knownNat @16
      inPortTLenBytes = LCLB.bitsToBytes $ WI.intValue $ inPortTLenBits
  v <- LCLM.doLoad bak mem sockaddrInPortPtr (LCLM.bitvectorType inPortTLenBytes)
                   (LCLM.LLVMPointerRepr inPortTLenBits) LCLD.noAlignment
  LCLM.projectLLVM_bv bak v

buildConnectOverride :: ( LCLM.HasPtrWidth w
                        , w ~ DMC.ArchAddrWidth arch
                        )
                     => FunctionOverride (AExt.AmbientSimulatorState sym arch) sym
                                         (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                       Ctx.::> LCLM.LLVMPointerType w
                                                       Ctx.::> LCLM.LLVMPointerType w) ext
                                         (LCLM.LLVMPointerType w)
buildConnectOverride = FunctionOverride
  { functionName = "connect"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callConnect bak) args
  }

-- | Override for the @connect@ function. This implementation is very simple, as
-- it only checks to see if the socket file descriptor argument has previously
-- been registered. If it has, it will return 0, indicating success. If not, it
-- will return -1, indicating failure.
--
-- Like @bind@, the @connect@ function also takes an @addr@ argument. However,
-- we never need to examine what port it uses, since this override always
-- assumes that the connection was successfully initiated (FD registration
-- notwithstanding).
callConnect :: ( LCB.IsSymBackend sym bak
               , sym ~ WE.ExprBuilder scope st fs
               , bak ~ LCBO.OnlineBackend solver scope st fs
               , WPO.OnlineSolver solver
               , LCLM.HasPtrWidth w
               , w ~ DMC.ArchAddrWidth arch
               )
            => bak
            -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
            -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
            -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
            -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                               (LCS.RegValue sym (LCLM.LLVMPointerType w))
callConnect bak sockfd _addr _addrlen = checkSocketFDInUse bak "connect" sockfd

buildListenOverride :: ( LCLM.HasPtrWidth w
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => FunctionOverride (AExt.AmbientSimulatorState sym arch) sym
                                        (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                      Ctx.::> LCLM.LLVMPointerType w) ext
                                        (LCLM.LLVMPointerType w)
buildListenOverride = FunctionOverride
  { functionName = "listen"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callListen bak) args
  }

-- | Override for the @listen@ function. This implementation is very simple, as
-- it only checks to see if the socket file descriptor argument has previously
-- been registered. If it has, it will return 0, indicating success. If not, it
-- will return -1, indicating failure.
callListen :: ( LCB.IsSymBackend sym bak
              , sym ~ WE.ExprBuilder scope st fs
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , WPO.OnlineSolver solver
              , LCLM.HasPtrWidth w
              , w ~ DMC.ArchAddrWidth arch
              )
           => bak
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                              (LCS.RegValue sym (LCLM.LLVMPointerType w))
callListen bak sockfd _backlog = checkSocketFDInUse bak "listen" sockfd

-- | Check if the socket file descriptor argument has previously been
-- registered. If so, return 0, indicating success. If not, return -1,
-- indicating failure.
--
-- This function is the workhorse for the @connect@ and @listen@ overrides.
checkSocketFDInUse :: ( LCB.IsSymBackend sym bak
                      , sym ~ WE.ExprBuilder scope st fs
                      , bak ~ LCBO.OnlineBackend solver scope st fs
                      , WPO.OnlineSolver solver
                      , LCLM.HasPtrWidth w
                      , w ~ DMC.ArchAddrWidth arch
                      )
                   => bak
                   -> T.Text
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                   -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                                      (LCS.RegValue sym (LCLM.LLVMPointerType w))
checkSocketFDInUse bak fnName sockfd = do
  let sym = LCB.backendGetSym bak
  sockfdInt <- liftIO $ networkConstantBVPtrToInteger bak fnName AE.FDArgument (LCS.regValue sockfd)
  serverSocketFDs <- Lens.use (LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs)
  ec <- if Map.member sockfdInt serverSocketFDs
        then returnIOSuccess
        else returnIOError
  liftIO $ bvToPtr sym ec ?ptrWidth

buildRecvOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                          Ctx.::> LCLM.LLVMPointerType w
                                                          Ctx.::> LCLM.LLVMPointerType w
                                                          Ctx.::> LCLM.LLVMPointerType w) ext
                                            (LCLM.LLVMPointerType w)
buildRecvOverride fs memVar = FunctionOverride
  { functionName = "recv"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callRecv fs memVar bak) args
  }

-- | Override for the @recv@ function. For now, we treat it identically to
-- @read@, ignoring the @flags@ argument entirely.
callRecv :: ( LCLM.HasLLVMAnn sym
            , LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            )
         => LCLS.LLVMFileSystem w
         -> LCS.GlobalVar LCLM.Mem
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callRecv fs memVar bak sockfd buf len _flags =
  ASO.callRead fs memVar bak sockfd buf len

buildSendOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                          Ctx.::> LCLM.LLVMPointerType w
                                                          Ctx.::> LCLM.LLVMPointerType w
                                                          Ctx.::> LCLM.LLVMPointerType w) ext
                                            (LCLM.LLVMPointerType w)
buildSendOverride fs memVar = FunctionOverride
  { functionName = "send"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callSend fs memVar bak) args
  }

-- | Override for the @send@ function. For now, we treat it identically to
-- @write@, ignoring the @flags@ argument entirely.
callSend :: ( LCLM.HasLLVMAnn sym
            , LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            )
         => LCLS.LLVMFileSystem w
         -> LCS.GlobalVar LCLM.Mem
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callSend fs memVar bak sockfd buf len _flags =
  ASO.callWrite fs memVar bak sockfd buf len

buildSocketOverride :: ( LCLM.HasPtrWidth w
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => LCLS.LLVMFileSystem w
                    -> FunctionOverride (AExt.AmbientSimulatorState sym arch) sym
                                        (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                      Ctx.::> LCLM.LLVMPointerType w
                                                      Ctx.::> LCLM.LLVMPointerType w) ext
                                        (LCLM.LLVMPointerType w)
buildSocketOverride fs = FunctionOverride
  { functionName = "socket"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callSocket fs bak) args
  }

-- | Override for the @socket@ function. This checks to see if the appropriate
-- arguments are concrete, and if so, open a file with the appropriate name
-- representing the socket. See Note @[The networking story]@ for the full
-- details.
callSocket :: ( LCB.IsSymBackend sym bak
              , sym ~ WE.ExprBuilder scope st fs
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , WPO.OnlineSolver solver
              , LCLM.HasPtrWidth w
              , w ~ DMC.ArchAddrWidth arch
              )
           => LCLS.LLVMFileSystem w
           -> bak
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim (AExt.AmbientSimulatorState sym arch) sym ext r args ret
                              (LCS.RegValue sym (LCLM.LLVMPointerType w))
callSocket fs bak domain typ _protocol = do
  let sym = LCB.backendGetSym bak
  domainInt <- liftIO $ networkConstantBVPtrToInteger bak "socket" AE.DomainArgument (LCS.regValue domain)
  domainText <-
    case Map.lookup domainInt socketDomainMap of
      Just d  -> pure d
      Nothing -> CMC.throwM $ AE.UnsupportedSocketArgument AE.DomainArgument domainInt
  typeInt <- liftIO $ networkConstantBVPtrToInteger bak "socket" AE.TypeArgument (LCS.regValue typ)
  typeText <-
    case Map.lookup typeInt socketTypeMap of
      Just t  -> pure t
      Nothing -> CMC.throwM $ AE.UnsupportedSocketArgument AE.TypeArgument typeInt
  let socketFileStr = "/network" FP.</> T.unpack domainText FP.</> T.unpack typeText FP.</> "socket"
  socketFileLit <- liftIO $ WI.stringLit sym $ WI.Char8Literal $ BS.pack socketFileStr
  fd <- LCSy.openFile (LCLS.llvmFileSystem fs) socketFileLit $ \res -> do
    case res of
      Left LCSy.FileNotFound -> returnIOError
      Right fileHandle -> do
        fd <- LCLS.allocateFileDescriptor fs fileHandle
        fdBV <- case WI.asBV fd of
          Just fdBV -> pure fdBV
          Nothing -> AP.panic AP.FunctionOverride "callSocket"
                              ["allocateFileDescriptor should return a concrete FD"]
        LCS.stateContext . LCS.cruciblePersonality . AExt.serverSocketFDs %=
          Map.insert (BVS.asUnsigned fdBV)
                     (ServerSocketInfo { serverSocketFilePath = socketFileStr
                                       , serverSocketPort = Nothing
                                       , serverSocketNextConnection = 0
                                       })
        pure fd
  liftIO $ bvToPtr sym fd ?ptrWidth

-- | A map of socket domains that the verifier supports. The keys are the
-- values of the corresponding C macros, with each key mapping to the name of
-- the macro.
--
-- Note that there is no guarantee that the values of these macros will be the
-- same in every OS/architecture configuration. At the moment, the values
-- happen to be the same in all of the configurations that the verifier
-- supports, so we have opted to hard-code the values for the time being. We
-- should eventually move towards a design that avoids this
-- hard-coding—see #75.
socketDomainMap :: Map.Map Integer T.Text
socketDomainMap = Map.fromList
  [ (2,  "AF_INET")
  , (10, "AF_INET6")
  ]

-- | A map of socket types that the verifier supports. The keys are the
-- values of the corresponding C macros, with each key mapping to the name of
-- the macro.
--
-- Note that there is no guarantee that the values of these macros will be the
-- same in every OS/architecture configuration. At the moment, the values
-- happen to be the same in all of the configurations that the verifier
-- supports, so we have opted to hard-code the values for the time being. We
-- should eventually move towards a design that avoids this
-- hard-coding—see #75.
socketTypeMap :: Map.Map Integer T.Text
socketTypeMap = Map.fromList
  [ (1, "SOCK_STREAM")
  , (2, "SOCK_DGRAM")
  , (5, "SOCK_SEQPACKET")
  ]

-- | Concretize a symbolic bitvector representing the argument to a
-- networking-related function override. If the bitvector is truly symbolic,
-- throw an appropriate exception.
networkConstantBV ::
     ( LCB.IsSymBackend sym bak
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , 1 WI.<= w
     )
  => bak
  -> T.Text
     -- ^ The name of the function being overriden. Only used for exception
     -- message purposes.
  -> AE.NetworkFunctionArgument
     -- ^ The sort of argument the 'WI.SymBV' represents. Only used for
     -- exception message purposes.
  -> WI.NatRepr w
     -- ^ The width of the bitvector.
  -> WI.SymBV sym w
     -- ^ The symbolic bitvector.
  -> IO (BVS.BV w)
networkConstantBV bak fnName fnArg w symBV = do
  -- NB: It's not enough to just use asBV here, as it's possible for these
  -- values to get spilled onto the stack. We need the power of an online
  -- solver connection in the general case.
  res <- AVC.resolveSymBVAs bak w symBV
  case res of
    Right bv -> pure bv
    Left AVC.SolverUnknown ->
      CMC.throwM $ AE.ConcretizationFailedUnknown target
    Left AVC.UnsatInitialAssumptions ->
      AP.panic AP.FunctionOverride "constantBV"
        ["Initial assumptions are unsatisfiable"]
    Left AVC.MultipleModels ->
      CMC.throwM $ AE.ConcretizationFailedSymbolic target
  where
    target = AE.NetworkFunction fnName fnArg

-- | Like 'networkConstantBV', but where:
--
-- * The argument is an 'LCLM.LLVMPtr' instead of a 'WI.SymBV'.
--
-- * The returned value is converted directly to an 'Integer'.
networkConstantBVPtrToInteger ::
     ( LCB.IsSymBackend sym bak
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , 1 WI.<= w
     )
  => bak
  -> T.Text
  -> AE.NetworkFunctionArgument
  -> LCLM.LLVMPtr sym w
  -> IO Integer
networkConstantBVPtrToInteger bak fnName fnArg ptr = do
  ptrBV <- LCLM.projectLLVM_bv bak ptr
  bv <- networkConstantBV bak fnName fnArg (LCLM.ptrWidth ptr) ptrBV
  pure $ BVS.asUnsigned bv

-- | Return 0, indicating success.
returnIOSuccess :: LCB.IsSymInterface sym
                => LCS.OverrideSim p sym ext r args ret (WI.SymBV sym 32)
returnIOSuccess = do
  sym <- LCS.getSymInterface
  liftIO $ WI.bvLit sym (WI.knownNat @32) (BVS.zero (WI.knownNat @32))

-- | Return 1, indiciating failure.
returnIOError :: LCB.IsSymInterface sym
              => LCS.OverrideSim p sym ext r args ret (WI.SymBV sym 32)
returnIOError = do
  sym <- LCS.getSymInterface
  liftIO $ WI.bvLit sym (WI.knownNat @32) (BVS.mkBV (WI.knownNat @32) (-1))

-------------------------------------------------------------------------------
-- Hacky Overrides
-------------------------------------------------------------------------------

-- These are crude overrides that are primarily meant as a shortcut to getting
-- something to work. We should replace these with proper solutions later.
-- See #19 for one possible way to do this.

hackyBumpMalloc :: ( LCB.IsSymBackend sym bak
                   , LCLM.HasPtrWidth w
                   )
                => bak
                -> LCS.GlobalVar (LCLM.LLVMPointerType w)
                -- ^ Global pointing to end of heap bump allocation
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -- ^ The number of bytes to allocate
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
hackyBumpMalloc bak endGlob (LCS.regValue -> sz) = do
  let sym = LCB.backendGetSym bak
  szBv <- liftIO $ LCLM.projectLLVM_bv bak sz
  LCS.modifyGlobal endGlob $ \endPtr -> liftIO $ do
    -- Bump up end pointer
    endPtr' <- LCLM.ptrSub sym ?ptrWidth endPtr szBv
    return (endPtr', endPtr')

buildHackyBumpMallocOverride
  :: LCLM.HasPtrWidth w
  => LCS.GlobalVar (LCLM.LLVMPointerType w)
  -- ^ Global pointing to end of heap bump allocation
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildHackyBumpMallocOverride endGlob = FunctionOverride
  { functionName = "malloc"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (hackyBumpMalloc bak endGlob) args
  }

hackyBumpCalloc :: ( LCB.IsSymBackend sym bak
                   , LCLM.HasLLVMAnn sym
                   , LCLM.HasPtrWidth w
                   )
                => bak
                -> LCS.GlobalVar (LCLM.LLVMPointerType w)
                -- ^ Global pointing to end of heap bump allocation
                -> LCS.GlobalVar LCLM.Mem
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -- ^ The number of elements in the array
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -- ^ The number of bytes to allocate
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
hackyBumpCalloc bak endGlob memVar (LCS.regValue -> num) (LCS.regValue -> sz) = do
  let sym = LCB.backendGetSym bak
  LCS.modifyGlobal endGlob $ \endPtr -> do
    res <- LCS.modifyGlobal memVar $ \mem -> liftIO $ do
      -- Bump up end pointer
      numBV <- LCLM.projectLLVM_bv bak num
      szBV  <- LCLM.projectLLVM_bv bak sz
      allocSzBv <- WI.bvMul sym numBV szBV
      endPtr' <- LCLM.ptrSub sym ?ptrWidth endPtr allocSzBv

      -- Zero memory
      zero <- WI.bvLit sym WI.knownNat (BVS.zero WI.knownNat)
      mem' <- LCLM.doMemset bak ?ptrWidth mem endPtr' zero allocSzBv
      return (endPtr', mem')
    return (res, res)

buildHackyBumpCallocOverride
  :: ( LCLM.HasLLVMAnn sym
     , LCLM.HasPtrWidth w
     )
  => LCS.GlobalVar (LCLM.LLVMPointerType w)
  -> LCS.GlobalVar LCLM.Mem
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                          Ctx.::> LCLM.LLVMPointerType w) ext
                            (LCLM.LLVMPointerType w)
buildHackyBumpCallocOverride endGlob memVar = FunctionOverride
  { functionName = "calloc"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (hackyBumpCalloc bak endGlob memVar) args
  }
