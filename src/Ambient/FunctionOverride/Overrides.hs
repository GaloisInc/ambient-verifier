{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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
  , buildMallocGlobalOverride
  , callMallocGlobal
  , buildCallocOverride
  , callCalloc
  , buildMemcpyOverride
  , callMemcpy
  , buildMemsetOverride
  , callMemset
    -- * Binary-related overrides
  , binOverrides
  , buildGetGlobalPointerAddrOverride
  , callGetGlobalPointerAddr
  , buildGetGlobalPointerNamedOverride
  , callGetGlobalPointerNamed
    -- * Printf-related overrides
  , module Ambient.FunctionOverride.Overrides.Printf
    -- * Crucible string–related overrides
  , module Ambient.FunctionOverride.Overrides.CrucibleStrings
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import           Data.Maybe ( mapMaybe )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as DT
import qualified Data.Text.Encoding as DTE
import qualified Data.Vector.NonEmpty as NEV
import qualified System.FilePath as SF

import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.BinaryLoader.ELF as DMBE
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic.MemOps as DMSM
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

import qualified Ambient.Exception as AE
import qualified Ambient.Extensions as AExt
import           Ambient.FunctionOverride
import           Ambient.FunctionOverride.Overrides.CrucibleStrings
import           Ambient.FunctionOverride.Overrides.Printf
import qualified Ambient.Loader.BinaryConfig as ALB
import qualified Ambient.Memory as AM
import qualified Ambient.MonadState as AMS
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
  FunctionOverrideContext arch ->
    -- In what context are the function overrides are being run?
  LCLS.LLVMFileSystem w ->
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  Map.Map (DMC.MemWord w) String ->
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  [SomeFunctionOverride (AExt.AmbientSimulatorState sym arch) sym ext]
allOverrides fovCtx fs initialMem unsupportedRelocs = concat
  [ -- Printf family
    printfFamilyOverrides initialMem unsupportedRelocs
    -- Crucible strings
  , crucibleStringOverrides initialMem unsupportedRelocs
    -- Memory
  , memOverrides initialMem
    -- Binary-related
  , binOverrides fovCtx initialMem
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
  , SomeFunctionOverride (buildMallocGlobalOverride memVar)
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

buildMallocGlobalOverride ::
  ( ?memOpts :: LCLM.MemOptions
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  ) =>
  LCS.GlobalVar LCLM.Mem ->
  FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext
                         (LCLM.LLVMPointerType w)
buildMallocGlobalOverride mvar =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "malloc-global" $ \bak args ->
    Ctx.uncurryAssignment (callMalloc bak mvar) args

-- | An override for a special @malloc-global@ function that is meant only to
-- be invoked from syntax overrides. @malloc-global@ is like @malloc@, but for
-- global memory. Implementation-wise, the only difference is that we pass
-- 'LCLM.GlobalAlloc' to 'LCLM.doMalloc' instead of 'LCLM.HeapAlloc' so that
-- Crucible can properly distinguish between the two kinds of memory.
callMallocGlobal ::
  ( LCB.IsSymBackend sym bak
  , ?memOpts :: LCLM.MemOptions
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  ) =>
  bak ->
  LCS.GlobalVar LCLM.Mem ->
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  -- ^ The number of bytes to allocate
  LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callMallocGlobal bak mvar (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let displayString = "<malloc-global function override>"
     szBV <- LCLM.projectLLVM_bv bak sz
     LCLM.doMalloc bak LCLM.GlobalAlloc LCLM.Mutable displayString mem szBV LCLD.noAlignment

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
     src' <- AMS.modifyM (liftIO . AExt.resolveAndPopulate bak mem0 initialMem szBV src)
     dest' <- AMS.modifyM (liftIO . AExt.resolveAndPopulate bak mem0 initialMem szBV dest)
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
        AMS.modifyM (liftIO . AExt.resolveAndPopulate bak mem0 initialMem szBV dest)
     mem1 <- LCS.readGlobal mvar
     mem2 <- liftIO $ LCLM.doMemset bak w mem1 dest' (LCS.regValue valBV) szBV
     pure ((), mem2)

-------------------------------------------------------------------------------
-- Binary-related overrides
-------------------------------------------------------------------------------

-- | All of the binary-related overrides, packaged up for your convenience.
binOverrides ::
  ( w ~ DMC.ArchAddrWidth arch
  , DMC.MemWidth w
  , LCLM.HasPtrWidth w
  ) =>
  FunctionOverrideContext arch ->
  -- ^ In what context are the overrides being run?
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  [SomeFunctionOverride p sym ext]
binOverrides fovCtx initialMem =
  [ SomeFunctionOverride $ buildGetGlobalPointerAddrOverride fovCtx initialMem
  , SomeFunctionOverride $ buildGetGlobalPointerNamedOverride fovCtx initialMem
  ]

buildGetGlobalPointerAddrOverride ::
  ( w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  , LCLM.HasPtrWidth w
  ) =>
  FunctionOverrideContext arch ->
  -- ^ In what context is this override being run?
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCT.StringType WI.Unicode
                                       Ctx.::> LCLM.LLVMPointerType w) ext
                         (LCLM.LLVMPointerType w)
buildGetGlobalPointerAddrOverride fovCtx initialMem =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "get-global-pointer-addr" $ \bak args ->
    Ctx.uncurryAssignment (callGetGlobalPointerAddr bak fovCtx initialMem) args

-- | Override for the @get-global-pointer-addr@ function. Note the following
-- invariants, which are checked in the implementation:
--
-- * Both arguments must be concrete.
--
-- * The 'FunctionOverrideContext' be a 'VerifyContext', as this override
--   requires information about binaries.
--
-- * The arguments must correspond to an actual binary and an actual address
--   within that binary.
callGetGlobalPointerAddr ::
  ( LCB.IsSymBackend sym bak
  , w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  ) =>
  bak ->
  FunctionOverrideContext arch ->
  -- ^ In what context is this override being run?
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  LCS.RegEntry sym (LCT.StringType WI.Unicode) ->
  -- ^ The binary in which the global variable is located
  LCS.RegEntry sym (LCLM.LLVMPointerType w) ->
  -- ^ The address of the global variable within that binary
  LCS.OverrideSim p sym ext r args ret (LCLM.LLVMPtr sym w)
callGetGlobalPointerAddr bak fovCtx initialMem
                         (LCS.regValue -> binName)
                         (LCS.regValue -> globAddr) = do
  let sym = LCB.backendGetSym bak
  -- Check that the address of the global variable is concrete.
  globAddrSymBV <- liftIO $ LCLM.projectLLVM_bv bak globAddr
  globAddrBV <- case WI.asBV globAddrSymBV of
                  Just bv -> pure bv
                  Nothing -> do
                    pl <- liftIO $ WI.getCurrentProgramLoc sym
                    CMC.throwM $ AE.ConcretizationFailedSymbolic pl
                               $ AE.GetGlobalPointerFunction
                                   AE.GetGlobalPointerAddr
                                   AE.GlobalAddrArgument
  let addr = fromInteger $ BVS.asUnsigned globAddrBV

  Some lbp <- findLoadedBinaryNamed sym fovCtx AE.GetGlobalPointerAddr binName
  resolveGlobalPointer initialMem AE.GetGlobalPointerAddr lbp addr

buildGetGlobalPointerNamedOverride ::
  ( w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  , LCLM.HasPtrWidth w
  ) =>
  FunctionOverrideContext arch ->
  AM.InitialMemory sym w ->
  FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCT.StringType WI.Unicode
                                       Ctx.::> LCT.StringType WI.Unicode) ext
                         (LCLM.LLVMPointerType w)
buildGetGlobalPointerNamedOverride fovCtx initialMem =
  WI.withKnownNat ?ptrWidth $
  mkFunctionOverride "get-global-pointer-named" $ \bak args ->
    Ctx.uncurryAssignment (callGetGlobalPointerNamed bak fovCtx initialMem) args

-- | Override for the @get-global-pointer-named@ function. Note the following
-- invariants, which are checked in the implementation:
--
-- * Both arguments must be concrete.
--
-- * The 'FunctionOverrideContext' be a 'VerifyContext', as this override
--   requires information about binaries.
--
-- * The arguments must correspond to an actual binary and an actual global
--   variable name within that binary.
--
-- * The function symbol for the global variable must be unversioned.
callGetGlobalPointerNamed ::
  ( LCB.IsSymBackend sym bak
  , w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  ) =>
  bak ->
  FunctionOverrideContext arch ->
  -- ^ In what context is this override being run?
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  LCS.RegEntry sym (LCT.StringType WI.Unicode) ->
  -- ^ The binary in which the global variable is located
  LCS.RegEntry sym (LCT.StringType WI.Unicode) ->
  -- ^ The name of the global variable within that binary
  LCS.OverrideSim p sym ext r args ret (LCLM.LLVMPtr sym w)
callGetGlobalPointerNamed bak fovCtx initialMem
                          (LCS.regValue -> binName)
                          (LCS.regValue -> globName) = do
  let sym = LCB.backendGetSym bak
  -- Check that the name of the global variable is concrete.
  globNameBS <- case WI.asString globName of
                  Just (WI.UnicodeLiteral globNameText) ->
                    pure $ DTE.encodeUtf8 globNameText
                  Nothing -> do
                    pl <- liftIO $ WI.getCurrentProgramLoc sym
                    CMC.throwM $ AE.ConcretizationFailedSymbolic pl
                               $ AE.GetGlobalPointerFunction
                                   AE.GetGlobalPointerNamed
                                   AE.GlobalNameArgument

  Some lbp <- findLoadedBinaryNamed sym fovCtx AE.GetGlobalPointerNamed binName

  -- Ensure that we can find an address corresponding to the global variable.
  addr <-
    case Map.lookup globNameBS (ALB.lbpGlobalVars lbp) of
      Just addr -> pure addr
      Nothing -> CMC.throwM $ AE.GetGlobalPointerGlobalNameNotFound
                                AE.GetGlobalPointerNamed globNameBS

  resolveGlobalPointer initialMem AE.GetGlobalPointerNamed lbp addr

-- | Concretize the argument representing the binary name and look up the
-- corresponding 'ALB.LoadedBinaryPath', throwing an exception if one of these
-- steps fails.
findLoadedBinaryNamed ::
  ( LCB.IsSymInterface sym
  , MonadIO m
  , CMC.MonadThrow m
  ) =>
  sym ->
  FunctionOverrideContext arch ->
  -- ^ In what context is this override being run?
  AE.GetGlobalPointerFunction ->
  -- ^ Is this @get-global-pointer-addr@ or @get-global-pointer-named@?
  WI.SymString sym WI.Unicode ->
  -- ^ The binary in which the global variable is located
  m (Some (ALB.LoadedBinaryPath arch))
findLoadedBinaryNamed sym fovCtx ggpFun binName = do
  -- Concretize the binary name.
  binPath <- case WI.asString binName of
               Just (WI.UnicodeLiteral binNameText) ->
                 pure $ DT.unpack binNameText
               Nothing -> do
                 pl <- liftIO $ WI.getCurrentProgramLoc sym
                 CMC.throwM $ AE.ConcretizationFailedSymbolic pl
                            $ AE.GetGlobalPointerFunction
                                ggpFun
                                AE.BinaryNameArgument

  -- Ensure that the supplied address actually exists within the binary.
  case fovCtx of
    VerifyContext binConf ->
      -- TODO: This requires searching through the binaries in order, which
      -- takes time linear to the number of binaries. We might want to cache
      -- which binary names map to which LoadedBinaryPaths somewhere in the
      -- BinaryConfig.
      case NEV.find (\lbp -> SF.takeFileName (ALB.lbpPath lbp) == binPath)
                    (ALB.bcBinaries binConf) of
        Just lbp -> pure $ Some lbp
        Nothing -> CMC.throwM $ AE.GetGlobalPointerBinaryNameNotFound ggpFun binPath
    TestContext -> CMC.throwM $ AE.GetGlobalPointerTestOverrides ggpFun

-- | Resolve the address of a global variable and a pointer to the variable.
resolveGlobalPointer ::
  ( LCB.IsSymInterface sym
  , w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  ) =>
  AM.InitialMemory sym w ->
  -- ^ Initial memory state for symbolic execution
  AE.GetGlobalPointerFunction ->
  -- ^ Is this @get-global-pointer-addr@ or @get-global-pointer-named@?
  ALB.LoadedBinaryPath arch binPath ->
  -- ^ The binary in which the global variable is located
  DMM.MemWord w ->
  -- ^ The address of the global variable within that binary
  LCS.OverrideSim p sym ext r args ret (LCLM.LLVMPtr sym w)
resolveGlobalPointer initialMem ggpFun lbp addr = do
  -- Ensure that the supplied address actually exists within the binary.
  let mem = DMB.memoryImage $ ALB.lbpBinary lbp
  addrSegOff <-
    case DMBE.resolveAbsoluteAddress mem addr of
      Just segOff -> pure segOff
      Nothing -> CMC.throwM $ AE.GetGlobalPointerGlobalAddrNotFound ggpFun addr

  -- Finally, return a pointer to the global variable.
  AMS.modifyM $ \st -> liftIO $
    DMSM.doGetGlobal st
                     (AM.imMemVar initialMem)
                     (AM.imGlobalMap initialMem)
                     (DMM.segoffAddr addrSegOff)
