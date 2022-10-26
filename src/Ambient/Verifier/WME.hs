{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.Verifier.WME (wmExecutor) where

import           Control.Applicative ( (<|>) )
import           Control.Lens ( (^.), (&), (.~), set )
import qualified Control.Monad.Reader as CMR
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.TraversableFC ( anyFC )
import qualified Data.Vector.NonEmpty as NEV
import           GHC.TypeNats ( KnownNat, type (<=) )
import qualified Lumberjack as LJ

import qualified Data.Macaw.Architecture.Info as DMAI
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Discovery.Classifier as DMDC
import qualified Data.Macaw.Discovery.ParsedContents as DMDP
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.CallFrame as LCSC
import qualified Lang.Crucible.Simulator.EvalStmt as LCSEv
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Extensions as AExt
import qualified Ambient.EventTrace as AET
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.Lift as AL
import qualified Ambient.Loader.BinaryConfig as ALB
import qualified Ambient.Memory as AM
import qualified Ambient.ObservableEvents as AO
import qualified Ambient.Panic as AP
import qualified Ambient.Verifier.SymbolicExecution as AVS
import qualified Ambient.Verifier.WMM as AVW

-- | An execution feature for following return oriented programs.  On each
-- return, this feature:
-- 1. Examines the instruction pointer 'ip'
-- 2. Disassembles the binary from 'ip'
-- 3. Lifts the disassembled function into a crucible CFG
-- 4. Returns a tail call to execute the CFG
wmeReturnFeature :: ( DMS.SymArchConstraints arch
                    , DMB.BinaryLoader arch binFmt
                    , ext ~ DMS.MacawExt arch
                    , LCB.IsSymInterface sym )
                 => DMAI.ArchitectureInfo arch
                 -> ALB.BinaryConfig arch binFmt
                 -- ^ Information about the loaded binaries
                 -> LCF.HandleAllocator
                 -> DMS.GenArchVals mem arch
                 -> sym
                 -> LCSEv.ExecutionFeature p sym ext rtp
wmeReturnFeature archInfo binConf hdlAlloc archVals sym = LCSEv.ExecutionFeature $ \estate -> do
  let regsRepr = LCT.StructRepr $ DMS.crucArchRegTypes $ DMS.archFunctions archVals
  case estate of
    LCSE.ReturnState _fnName ctx regs state
      | Just PC.Refl <- PC.testEquality regsRepr (LCS.regType regs) ->
        case LCS.regValue (DMS.lookupReg archVals regs DMC.ip_reg) of
          LCLM.LLVMPointer _ ipVal -> do
            symNatAddr <- WI.bvToNat sym ipVal
            case WI.asNat symNatAddr of
              Just addr -> do
                (funcAddrOff, binIndex) <- AVS.resolveFuncAddrFromBinaries binConf (fromIntegral addr)
                let loadedBinaryPath = ALB.bcBinaries binConf NEV.! binIndex
                LCCC.SomeCFG cfg <- buildCfgFromAddr archInfo loadedBinaryPath hdlAlloc funcAddrOff archVals
                let blockId = LCCC.cfgEntryBlockID cfg
                let postdom = LCAP.postdomInfo cfg
                let regMap = LCS.RegMap (Ctx.empty Ctx.:> regs)
                let callFrame = LCSC.mkCallFrame cfg postdom regMap
                let call = LCSE.CrucibleCall blockId callFrame
                let tailCallState = LCSE.TailCallState ctx call state
                return $ LCSEv.ExecutionFeatureNewState tailCallState
              Nothing -> AP.panic AP.WME
                                  "wmeReturnFeature"
                                  [  "Encountered symbolic instruction pointer: "
                                  ++ (show (WI.printSymExpr ipVal)) ]
    _ -> return LCSEv.ExecutionFeatureNoChange

-- | Given an address and a binary, this function builds a CFG for the function
-- at the given address.
buildCfgFromAddr :: forall arch binFmt w mem
                  . ( w ~ DMC.ArchAddrWidth arch
                    , DMB.BinaryLoader arch binFmt
                    , KnownNat w
                    , 1 <= w )
                 => DMAI.ArchitectureInfo arch
                 -> ALB.LoadedBinaryPath arch binFmt
                 -- ^ Binary to disassemble
                 -> LCF.HandleAllocator
                 -> DMC.MemSegmentOff w
                 -- ^ Address to disassemble from
                 -> DMS.GenArchVals mem arch
                 -> IO (LCCC.SomeCFG (DMS.MacawExt arch)
                                     (Ctx.EmptyCtx Ctx.::> DMS.ArchRegStruct arch)
                                     (DMS.ArchRegStruct arch))
buildCfgFromAddr archInfo loadedBinaryPath hdlAlloc funcAddrOff archVals =
  lift ((discoveryState ^. DMD.funInfo) Map.! funcAddrOff)
  where
    mem = DMB.memoryImage $ ALB.lbpBinary loadedBinaryPath
    symMap = ALB.lbpAddrSymMap loadedBinaryPath
    pltEntryPoints = ALB.lbpTrustedPltEntryPoints loadedBinaryPath
    discoveryState = DMD.cfgFromAddrs archInfo mem symMap [funcAddrOff] []
                       & DMD.trustedFunctionEntryPoints .~ pltEntryPoints

    -- Lift a disassembled function to a crucible CFG
    lift (Some fn) =
      AL.liftDiscoveredFunction hdlAlloc "weird-machine" (DMS.archFunctions archVals) fn

-- | This function is used to look up a function handle when a call is
-- encountered within a weird machine.  Because 'wmeReturnFeature' flags all
-- ROP gadgets as ending in a tail call, this function is also called at the
-- end of each gadget to disassemble and jump to the next gadget.
--
-- This is very similar to 'AVS.symExLookupFunction' except that this has the
-- capability to rebuild CFGs from the middle of a function.
wmeLookupFunction
  :: forall arch mem binFmt w p sym bak solver scope st fs
   . ( w ~ DMC.ArchAddrWidth arch
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , sym ~ WE.ExprBuilder scope st fs
     , p ~ AExt.AmbientSimulatorState sym arch
     , DMS.SymArchConstraints arch
     , LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , WPO.OnlineSolver solver
     , DMB.BinaryLoader arch binFmt
     )
  => LJ.LogAction IO AD.Diagnostic
  -> bak
  -> AM.InitialMemory sym w
  -> DMS.GenArchVals mem arch
  -> ALB.BinaryConfig arch binFmt
  -- ^ Information about the loaded binaries
  -> AF.FunctionABI arch sym p
  -- ^ Function call ABI specification for 'arch'
  -> LCF.HandleAllocator
  -> DMAI.ArchitectureInfo arch
  -> AET.Properties
  -- ^ The properties to be checked, along with their corresponding global traces
  -> Maybe FilePath
  -- ^ Optional path to the file to log function calls to
  -> AO.ObservableEventConfig sym
  -- ^ Configuration to use for observable event tracing
  -> DMS.LookupFunctionHandle p sym arch
wmeLookupFunction logAction bak initialMem archVals binConf abi hdlAlloc archInfo props mFnCallLog oec =
  AVS.lookupFunction buildCfg logAction bak initialMem archVals binConf abi hdlAlloc props mFnCallLog oec
  where
    buildCfg :: DMC.MemSegmentOff w
             -- ^ The address offset
             -> ALB.LoadedBinaryPath arch binFmt
             -- ^ The binary that the address resides in
             -> IO (LCCC.SomeCFG (DMS.MacawExt arch)
                                 (Ctx.EmptyCtx Ctx.::> DMS.ArchRegStruct arch)
                                 (DMS.ArchRegStruct arch))
    buildCfg funcAddrOff bin =
      buildCfgFromAddr archInfo bin hdlAlloc funcAddrOff archVals

-- | This classifier identifies gadgets in which the instruction pointer at the
-- end of the block is either read from memory, or computed from a memory read.
-- We expect existing classifiers to handle cases where the instruction pointer
-- is a constant.
--
-- The goal of this architecture agnostic classifier is to capture instances of
-- calls, returns, and indirect branches that may be missed by Macaw.  Further
-- relaxing of the classifier may require architecture specific gadget
-- classifiers that inspect the instructions themselves (much like the
-- architecture specific call and return classifiers that Macaw employs).
weirdClassifier :: DMD.BlockClassifier arch ids
weirdClassifier = DMAI.classifierName "Weird gadget" $ do
  bcc <- CMR.ask
  let ctx = DMAI.classifierParseContext bcc
  DMAI.withArchConstraints (DMAI.pctxArchInfo ctx) $ do
    let regs = DMAI.classifierFinalRegState bcc
    let blockEnd = DMDC.classifierEndBlock bcc
    let ipVal = regs ^. DMC.boundValue DMC.ip_reg
    if containsReadMem ipVal
    then pure $ DMDP.ParsedContents {
             DMDP.parsedNonterm = F.toList (DMAI.classifierStmts bcc)
           , DMDP.parsedTerm  = DMDP.ParsedCall regs Nothing
           , DMDP.writtenCodeAddrs =
             filter (\a -> DMC.segoffAddr a /= blockEnd) $
             DMAI.classifierWrittenAddrs bcc
           , DMDP.intraJumpTargets = []
           , DMDP.newFunctionAddrs = []
           }
    else fail "ip is not read from memory"
  where
    containsReadMem :: DMC.Value arch ids tp -> Bool
    containsReadMem val =
      case DMC.valueAsRhs val of
        Just (DMC.ReadMem {}) -> True
        Just (DMC.CondReadMem {}) -> True
        Just (DMC.EvalApp app) -> anyFC containsReadMem app
        _ -> False


-- | Produces a 'WMMCallback' for symbolically executing weird machines.  This
-- callback disassembles from the entry point of the weird machine, constructs
-- a crucible CFG, and then symbolically executes the CFG.
--
-- Currently this only supports return oriented programs, but could be extended
-- to support other types of weird machines.
wmExecutor :: forall arch binFmt w p bak sym mem solver scope st fs
            . ( w ~ DMC.ArchAddrWidth arch
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , sym ~ WE.ExprBuilder scope st fs
              , p ~ AExt.AmbientSimulatorState sym arch
              , DMS.SymArchConstraints arch
              , 1 <= w
              , KnownNat w
              , LCB.IsSymInterface sym
              , LCLM.HasLLVMAnn sym
              , DMB.BinaryLoader arch binFmt
              , WPO.OnlineSolver solver
              )
           => LJ.LogAction IO AD.Diagnostic
           -> bak
           -> AM.InitialMemory sym w
           -> ALB.BinaryConfig arch binFmt
           -- ^ Information about the loaded binaries
           -> AF.FunctionABI arch sym p
           -- ^ Function call ABI specification for 'arch'
           -> LCF.HandleAllocator
           -> DMAI.ArchitectureInfo arch
           -> AET.Properties
           -- ^ The properties to be checked, along with their corresponding global traces
           -> DMS.GenArchVals mem arch
           -> Maybe FilePath
           -- ^ Optional path to the file to log function calls to
           -> AO.ObservableEventConfig sym
           -- ^ Configuration to use for observable event tracing
           -> [LCS.GenericExecutionFeature sym]
           -- ^ Additional execution features to use when executing the weird
           -- machine
           -> AVW.WMMCallback arch sym
wmExecutor logAction bak initialMem binConf abi hdlAlloc archInfo props archVals mFnCallLog oec execFeatures = AVW.WMMCallback $ \addr st -> do
  let sym = LCB.backendGetSym bak
  let archInfo' = archInfo { DMAI.archClassifier = DMAI.archClassifier archInfo
                                               <|> weirdClassifier }
  let lookupFn = wmeLookupFunction logAction bak initialMem archVals binConf abi hdlAlloc archInfo' props mFnCallLog oec
  (funcAddrOff, binIndex) <- AVS.resolveFuncAddrFromBinaries binConf addr
  let loadedBinaryPath = ALB.bcBinaries binConf NEV.! binIndex
  LCCC.SomeCFG cfg <- buildCfgFromAddr archInfo' loadedBinaryPath hdlAlloc funcAddrOff archVals
  let ctx' = set (LCS.cruciblePersonality . AExt.overrideLookupFunctionHandle)
                 (Just lookupFn)
                 (st ^. LCS.stateContext)
  let globals = st ^. LCSE.stateGlobals
  let regsRepr = LCT.StructRepr $ DMS.crucArchRegTypes $ DMS.archFunctions archVals
  case st ^. LCSE.stateTree . LCSE.actFrame . LCS.gpValue of
    LCSC.RF _ reg ->
      case PC.testEquality regsRepr (LCS.regType reg) of
        Just PC.Refl -> do
          let simAction = LCS.runOverrideSim regsRepr (LCS.regValue <$> LCS.callCFG cfg (LCS.RegMap (Ctx.empty Ctx.:> reg)))
          let st' = LCS.InitialState ctx' globals LCS.defaultAbortHandler regsRepr simAction
          let executionFeatures = (wmeReturnFeature archInfo' binConf hdlAlloc archVals sym) : fmap LCS.genericToExecutionFeature execFeatures
          res <- LCS.executeCrucible executionFeatures st'
          return $ AVW.WMMResultCompleted res
        _ -> AP.panic AP.WME "wmExecutor" ["Unexpected register shape"]

    -- NOTE: Because the executor returns 'WMMResultNoChange' for
    -- everything but 'RF' types, the executor only works for return
    -- oriented programs.  Adding a branch for 'MF' types is required to
    -- support call oriented weird machines.
    _ -> return AVW.WMMResultNoChange
