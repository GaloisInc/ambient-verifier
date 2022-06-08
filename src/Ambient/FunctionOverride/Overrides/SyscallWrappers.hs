{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Overrides for functions that act as thin wrappers around system calls.
-- It is helpful to have both forms of overrides since the wrapper functions
-- can sometimes perform other actions that are difficult to simulate (e.g.,
-- @pthread@-related configuration).
module Ambient.FunctionOverride.Overrides.SyscallWrappers
  ( syscallWrapperOverrides
  , buildExecveOverride
  , buildNoOpMkdirOverride
  , exitOverride
  , getppidOverride
  , buildReadOverride
  , buildWriteOverride
  , buildOpenOverride
  , buildCloseOverride
  , buildShmgetOverride
  , shmatOverride
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT

import qualified Ambient.Extensions as AExt
import           Ambient.FunctionOverride
import qualified Ambient.Memory as AM
import qualified Ambient.Syscall.Overrides as ASO

-- | All of the socket I/O–related overrides, packaged up for your
-- convenience.
syscallWrapperOverrides ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  ) =>
  LCLS.LLVMFileSystem w ->
  AM.InitialMemory sym w ->
  Map.Map (DMC.MemWord w) String ->
  [SomeFunctionOverride (AExt.AmbientSimulatorState sym arch) sym ext]
syscallWrapperOverrides fs initialMem unsupportedRelocs =
  [ SomeFunctionOverride buildExecveOverride
  , SomeFunctionOverride exitOverride
  , SomeFunctionOverride getppidOverride
  , SomeFunctionOverride (buildReadOverride fs memVar)
  , SomeFunctionOverride (buildWriteOverride fs memVar)
  , SomeFunctionOverride (buildOpenOverride fs initialMem unsupportedRelocs)
  , SomeFunctionOverride (buildCloseOverride fs memVar)
  , SomeFunctionOverride (buildShmgetOverride memVar)
  , SomeFunctionOverride shmatOverride
  , SomeFunctionOverride (buildAcceptOverride fs)
  , SomeFunctionOverride (buildBindOverride fs initialMem unsupportedRelocs)
  , SomeFunctionOverride buildConnectOverride
  , SomeFunctionOverride buildListenOverride
  , SomeFunctionOverride (buildRecvOverride fs memVar)
  , SomeFunctionOverride (buildSendOverride fs memVar)
  , SomeFunctionOverride (buildSocketOverride fs)
    -- FIXME: This no-op override is for tracking purposes
    -- only.  It should be replaced with a more faithful
    -- override at some point.
  , SomeFunctionOverride buildNoOpMkdirOverride
  ]
  where
    memVar = AM.imMemVar initialMem

buildExecveOverride :: LCLM.HasPtrWidth w
                    => FunctionOverride p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType w)
buildExecveOverride = syscallToFunctionOverride ASO.buildExecveOverride

buildNoOpMkdirOverride :: LCLM.HasPtrWidth w
                       => FunctionOverride p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType w)
buildNoOpMkdirOverride = syscallToFunctionOverride ASO.buildNoOpMkdirOverride

exitOverride :: forall p sym ext w
              . LCLM.HasPtrWidth w
             => FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext LCT.UnitType
exitOverride = syscallToFunctionOverride ASO.exitOverride

getppidOverride :: LCLM.HasPtrWidth w
                => FunctionOverride p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType w)
getppidOverride = syscallToFunctionOverride ASO.getppidOverride

buildReadOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> FunctionOverride p
                       sym
                       (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                     Ctx.::> LCLM.LLVMPointerType w
                                     Ctx.::> LCLM.LLVMPointerType w)
                       ext
                       (LCLM.LLVMPointerType w)
buildReadOverride fs memVar = syscallToFunctionOverride $ ASO.buildReadOverride fs memVar

buildWriteOverride :: ( LCLM.HasLLVMAnn sym
                      , LCLM.HasPtrWidth w
                      )
                   => LCLS.LLVMFileSystem w
                   -> LCS.GlobalVar LCLM.Mem
                   -> FunctionOverride
                        p
                        sym
                        (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                      Ctx.::> LCLM.LLVMPointerType w
                                      Ctx.::> LCLM.LLVMPointerType w)
                        ext
                        (LCLM.LLVMPointerType w)
buildWriteOverride fs memVar = syscallToFunctionOverride $ ASO.buildWriteOverride fs memVar

buildOpenOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     , p ~ AExt.AmbientSimulatorState sym arch
                     , DMC.MemWidth w
                     , w ~ DMC.ArchAddrWidth arch
                     )
                  => LCLS.LLVMFileSystem w
                  -> AM.InitialMemory sym w
                  -> Map.Map (DMC.MemWord w) String
                  -> FunctionOverride
                       p
                       sym
                       (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                     Ctx.::> LCLM.LLVMPointerType w)
                       ext
                       (LCLM.LLVMPointerType w)
buildOpenOverride fs initialMem unsupportedRelocs =
  syscallToFunctionOverride $ ASO.buildOpenOverride fs initialMem unsupportedRelocs

buildCloseOverride :: ( LCLM.HasLLVMAnn sym
                      , LCLM.HasPtrWidth w
                      )
                   => LCLS.LLVMFileSystem w
                   -> LCS.GlobalVar LCLM.Mem
                   -> FunctionOverride
                        p
                        sym
                        (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                        ext
                        (LCLM.LLVMPointerType w)
buildCloseOverride fs memVar = syscallToFunctionOverride $ ASO.buildCloseOverride fs memVar

shmatOverride :: ( LCLM.HasLLVMAnn sym
                 , LCLM.HasPtrWidth w
                 , p ~ AExt.AmbientSimulatorState sym arch
                 , w ~ DMC.ArchAddrWidth arch
                 )
              => FunctionOverride
                   p
                   sym
                   (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                 Ctx.::> LCLM.LLVMPointerType w
                                 Ctx.::> LCLM.LLVMPointerType w)
                   ext
                   (LCLM.LLVMPointerType w)
shmatOverride = syscallToFunctionOverride ASO.shmatOverride

buildShmgetOverride :: ( LCLM.HasLLVMAnn sym
                       , LCLM.HasPtrWidth w
                       , p ~ AExt.AmbientSimulatorState sym arch
                       , w ~ DMC.ArchAddrWidth arch
                       )
                  => LCS.GlobalVar LCLM.Mem
                  -> FunctionOverride
                       p
                       sym
                       (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                     Ctx.::> LCLM.LLVMPointerType w
                                     Ctx.::> LCLM.LLVMPointerType w)
                       ext
                       (LCLM.LLVMPointerType w)
buildShmgetOverride memVar = syscallToFunctionOverride $ ASO.buildShmgetOverride memVar

buildAcceptOverride :: ( LCLM.HasPtrWidth w
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => LCLS.LLVMFileSystem w
                    -> FunctionOverride
                         (AExt.AmbientSimulatorState sym arch) sym
                         (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                       Ctx.::> LCLM.LLVMPointerType w
                                       Ctx.::> LCLM.LLVMPointerType w) ext
                         (LCLM.LLVMPointerType w)
buildAcceptOverride fs = syscallToFunctionOverride $ ASO.buildAcceptOverride fs

buildBindOverride :: ( LCLM.HasPtrWidth w
                     , LCLM.HasLLVMAnn sym
                     , DMC.MemWidth w
                     , w ~ DMC.ArchAddrWidth arch
                     )
                  => LCLS.LLVMFileSystem w
                  -> AM.InitialMemory sym w
                  -- ^ Initial memory state for symbolic execution
                  -> Map.Map (DMC.MemWord w) String
                  -- ^ Mapping from unsupported relocation addresses to the names of the
                  -- unsupported relocation types.
                  -> FunctionOverride
                       (AExt.AmbientSimulatorState sym arch) sym
                       (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                     Ctx.::> LCLM.LLVMPointerType w
                                     Ctx.::> LCLM.LLVMPointerType w) ext
                       (LCLM.LLVMPointerType w)
buildBindOverride fs initialMem unsupportedRelocs =
  syscallToFunctionOverride $ ASO.buildBindOverride fs initialMem unsupportedRelocs

buildConnectOverride :: ( LCLM.HasPtrWidth w
                        , w ~ DMC.ArchAddrWidth arch
                        )
                     => FunctionOverride
                          (AExt.AmbientSimulatorState sym arch) sym
                          (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                        Ctx.::> LCLM.LLVMPointerType w
                                        Ctx.::> LCLM.LLVMPointerType w) ext
                          (LCLM.LLVMPointerType w)
buildConnectOverride = syscallToFunctionOverride ASO.buildConnectOverride

buildListenOverride :: ( LCLM.HasPtrWidth w
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => FunctionOverride
                         (AExt.AmbientSimulatorState sym arch) sym
                         (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                       Ctx.::> LCLM.LLVMPointerType w) ext
                         (LCLM.LLVMPointerType w)
buildListenOverride = syscallToFunctionOverride ASO.buildListenOverride

buildRecvOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> FunctionOverride
                       p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w) ext
                             (LCLM.LLVMPointerType w)
buildRecvOverride fs memVar =
  syscallToFunctionOverride $ ASO.buildRecvOverride fs memVar

buildSendOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> FunctionOverride
                       p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w) ext
                             (LCLM.LLVMPointerType w)
buildSendOverride fs memVar =
  syscallToFunctionOverride $ ASO.buildSendOverride fs memVar

buildSocketOverride :: ( LCLM.HasPtrWidth w
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => LCLS.LLVMFileSystem w
                    -> FunctionOverride
                         (AExt.AmbientSimulatorState sym arch) sym
                         (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                       Ctx.::> LCLM.LLVMPointerType w
                                       Ctx.::> LCLM.LLVMPointerType w) ext
                         (LCLM.LLVMPointerType w)
buildSocketOverride fs = syscallToFunctionOverride $ ASO.buildSocketOverride fs
