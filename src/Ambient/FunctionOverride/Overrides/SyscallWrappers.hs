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
