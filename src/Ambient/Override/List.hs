{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Ambient.Override.List
  ( listOverrides
  , module Ambient.Override.List.Types
  ) where

import           Control.Monad.IO.Class ( MonadIO(..) )
import qualified Data.Map as Map
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Lumberjack as LJ

import qualified Data.Macaw.Architecture.Info as DMAI
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.SymIO as LCSy
import qualified Lang.Crucible.SymIO.Loader as LCSL
import qualified What4.Interface as WI

import qualified Ambient.Diagnostic as AD
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.Extension as AFE
import qualified Ambient.Loader as AL
import qualified Ambient.Loader.BinaryConfig as ALB
import qualified Ambient.Memory as AM
import           Ambient.Override.List.Types
import qualified Ambient.Solver as AS
import qualified Ambient.Syscall as ASy
import qualified Ambient.Verifier as AV
import qualified Ambient.Verifier.WMM as AVW
import qualified Ambient.Verifier.SymbolicExecution as AVS

-- | List all of the overrides that are registered for verifying a binary,
-- without actually verifying the binary.

-- It's surprisingly complicated to implement this, primarily by virtue of the
-- fact that we have to construct all of the arguments needed for
-- 'buildFunctionABI' and 'buildSyscallABI'. Issue #131 explores the
-- possibility of refactoring things to make this simpler to implement.
listOverrides :: LJ.LogAction IO AD.Diagnostic
              -> AV.ProgramInstance
              -> IO ()
listOverrides logAction pinst = do
  hdlAlloc <- liftIO LCF.newHandleAllocator
  Some ng <- liftIO PN.newIONonceGenerator
  AS.withOnlineSolver (AV.piSolver pinst) (AV.piFloatMode pinst) ng $ \bak ->
    let sym = LCB.backendGetSym bak in
    AL.withBinary (AV.piPath pinst) (AV.piBinary pinst) (AV.piSharedObjectDir pinst) hdlAlloc sym $
        \(archInfo :: DMAI.ArchitectureInfo arch) _archVals
        (ASy.BuildSyscallABI buildSyscallABI) (AF.BuildFunctionABI buildFunctionABI)
        parserHooks buildGlobals _numBytes binConf -> do
      functionOvs <- case AV.piOverrideDir pinst of
        Just dir -> do
          liftIO $ AFE.loadCrucibleSyntaxOverrides dir ng hdlAlloc parserHooks
        Nothing -> return []
      let mems = fmap (DMB.memoryImage . ALB.lbpBinary) (ALB.bcBinaries binConf)
      let ?memOpts = LCLM.defaultMemOptions
      initialMem <- AVS.initializeMemory bak hdlAlloc archInfo mems buildGlobals functionOvs Map.empty
      fileContents <- liftIO $
        case AV.piFsRoot pinst of
          Nothing -> return LCSy.emptyInitialFileSystemContents
          Just fsRoot -> LCSL.loadInitialFiles sym fsRoot
      let ?ptrWidth = WI.knownNat @(DMC.ArchAddrWidth arch)
      (fs, globals0, LCLS.SomeOverrideSim _initFSOverride) <- liftIO $
        LCLS.initialLLVMFileSystem hdlAlloc sym WI.knownRepr fileContents [] (AM.imGlobals initialMem)
      (wmConfig, _globals1) <- liftIO $ AVW.initWMConfig sym hdlAlloc globals0 (AV.piProperties pinst)
      let syscallABI = buildSyscallABI fs initialMem Map.empty (AVW.wmProperties wmConfig)
      let functionABI = buildFunctionABI fs initialMem Map.empty functionOvs Map.empty

      let ?recordLLVMAnnotation = \_ _ _ -> return ()
      let ols = mkOverrideLists syscallABI functionABI
      LJ.writeLog logAction $ AD.ListingOverrides ols
