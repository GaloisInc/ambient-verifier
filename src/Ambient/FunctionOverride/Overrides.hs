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
  ( allOverrides
    -- * Memory-related overrides
  , memOverrides
  , buildMallocOverride
  , callMalloc
  , buildCallocOverride
  , callCalloc
  , buildMemcpyOverride
  , callMemcpy
  , buildMemsetOverride
  , callMemset
  -- * Printf-related overrides
  , module Ambient.FunctionOverride.Overrides.Printf
    -- * Crucible string–related overrides
  , module Ambient.FunctionOverride.Overrides.CrucibleStrings
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.State as CMS
import qualified Data.Map.Strict as Map
import           Data.Maybe ( mapMaybe )
import qualified Data.Parameterized.Context as Ctx

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Ambient.Extensions as AExt
import           Ambient.FunctionOverride
import           Ambient.FunctionOverride.Overrides.CrucibleStrings
import           Ambient.FunctionOverride.Overrides.Printf
import qualified Ambient.Memory as AM
import           Ambient.Override
import qualified Ambient.Syscall as AS
import qualified Ambient.Syscall.Overrides as ASO

-------------------------------------------------------------------------------
-- Memory-related overrides
-------------------------------------------------------------------------------

-- | All of the overrides that work across all supported configurations.
allOverrides ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  LCLS.LLVMFileSystem w ->
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  Map.Map (DMC.MemWord w) String ->
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  [SomeFunctionOverride (AExt.AmbientSimulatorState sym arch) sym ext]
allOverrides fs initialMem unsupportedRelocs = concat
  [ -- Printf
    [SomeFunctionOverride (buildSprintfOverride initialMem unsupportedRelocs)]
    -- Crucible strings
  , crucibleStringOverrides initialMem unsupportedRelocs
    -- Memory
  , memOverrides initialMem
    -- Syscall wrappers
  , syscallWrapperOverrides
  ]
  where
    syscallWrapperOverrides =
      mapMaybe (\(AS.SomeSyscall syscall) ->
                 if AS.syscallHasWrapperFunction syscall
                    then Just $ SomeFunctionOverride $ syscallToFunctionOverride syscall
                    else Nothing)
               (ASO.allOverrides fs initialMem unsupportedRelocs)

-- | All of the memory-related overrides, packaged up for your convenience.
memOverrides ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , DMC.MemWidth w
  , w ~ DMC.ArchAddrWidth arch
  , ?memOpts :: LCLM.MemOptions
  ) =>
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  [SomeFunctionOverride (AExt.AmbientSimulatorState sym arch) sym ext]
memOverrides initialMem =
  [ SomeFunctionOverride (buildCallocOverride memVar)
  , SomeFunctionOverride (buildMallocOverride memVar)
  , SomeFunctionOverride (buildMemcpyOverride initialMem)
  , SomeFunctionOverride (buildMemsetOverride initialMem)
  ]
  where
    memVar = AM.imMemVar initialMem

buildCallocOverride :: ( LCLM.HasLLVMAnn sym
                       , ?memOpts :: LCLM.MemOptions
                       , LCLM.HasPtrWidth w
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildCallocOverride mvar =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "calloc" $ \bak args ->
    Ctx.uncurryAssignment (callCalloc bak mvar) args

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

-- | Given a function that modifies state, this function wraps the call in
-- @get@ and @put@ operations to update the state in the state monad.
modifyM :: (CMS.MonadState s m) => (s -> m (a, s)) -> m a
modifyM fn = do
  s <- CMS.get
  (a, s') <- fn s
  CMS.put s'
  return a

buildMallocOverride :: ( ?memOpts :: LCLM.MemOptions
                       , LCLM.HasLLVMAnn sym
                       , LCLM.HasPtrWidth w
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildMallocOverride mvar =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "malloc" $ \bak args ->
    Ctx.uncurryAssignment (callMalloc bak mvar) args

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
                       , DMC.MemWidth w
                       , p ~ AExt.AmbientSimulatorState sym arch
                       , w ~ DMC.ArchAddrWidth arch
                       )
                    => AM.InitialMemory sym w
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              LCT.UnitType
buildMemcpyOverride initialMem =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "memcpy" $ \bak args ->
    Ctx.uncurryAssignment (callMemcpy bak initialMem) args

-- | Override for the @memcpy@ function. This behaves identically to the
-- corresponding override in @crucible-llvm@.
callMemcpy :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              , LCLM.HasLLVMAnn sym
              , DMC.MemWidth w
              , p ~ AExt.AmbientSimulatorState sym arch
              , sym ~ WE.ExprBuilder scope st fs
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , w ~ DMC.ArchAddrWidth arch
              , WPO.OnlineSolver solver
              )
           => bak
           -> AM.InitialMemory sym w
           -- ^ Initial memory state for symbolic execution
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim p sym ext r args ret ()
callMemcpy bak initialMem dest src (LCS.regValue -> sz) =
  LCS.modifyGlobal (AM.imMemVar initialMem) $ \mem0 ->
  do szBV <- liftIO $ LCLM.projectLLVM_bv bak sz
     let ?memOpts = overrideMemOptions
     src' <- modifyM (liftIO . AExt.resolveAndPopulate bak mem0 initialMem szBV src)
     dest' <- modifyM (liftIO . AExt.resolveAndPopulate bak mem0 initialMem szBV dest)
     mem1 <- LCS.readGlobal (AM.imMemVar initialMem)
     mem2 <- liftIO $ LCLM.doMemcpy bak (LCLM.ptrWidth sz) mem1 True dest' src' szBV
     pure ((), mem2)

buildMemsetOverride :: ( LCLM.HasPtrWidth w
                       , LCLM.HasLLVMAnn sym
                       , p ~ AExt.AmbientSimulatorState sym arch
                       , w ~ DMC.ArchAddrWidth arch
                       , DMC.MemWidth w
                       )
                    => AM.InitialMemory sym w
                    -- ^ Initial memory state for symbolic execution
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              LCT.UnitType
buildMemsetOverride initialMem =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "memset" $ \bak args ->
    Ctx.uncurryAssignment (callMemset bak initialMem) args

-- | Override for the @memset@ function. This behaves identically to the
-- corresponding override in @crucible-llvm@.
callMemset :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              , LCLM.HasLLVMAnn sym
              , sym ~ WE.ExprBuilder scope st fs
              , p ~ AExt.AmbientSimulatorState sym arch
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , w ~ DMC.ArchAddrWidth arch
              , WPO.OnlineSolver solver
              , DMC.MemWidth w
              )
           => bak
           -> AM.InitialMemory sym w
           -- ^ Initial memory state for symbolic execution
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim p sym ext r args ret ()
callMemset bak initialMem dest val (LCS.regValue -> sz) =
  let mvar = AM.imMemVar initialMem in
  LCS.modifyGlobal mvar $ \mem0 ->
  do let w = LCLM.ptrWidth sz
     valBV <- liftIO $ ptrToBv8 bak w val
     szBV <- liftIO $ LCLM.projectLLVM_bv bak sz
     dest' <-
        modifyM (liftIO . AExt.resolveAndPopulate bak mem0 initialMem szBV dest)
     mem1 <- LCS.readGlobal mvar
     mem2 <- liftIO $ LCLM.doMemset bak w mem1 dest' (LCS.regValue valBV) szBV
     pure ((), mem2)
