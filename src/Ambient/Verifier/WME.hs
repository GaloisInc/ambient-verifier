{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.Verifier.WME (wmExecutor) where

import           Control.Applicative ( (<|>) )
import           Control.Lens ( (^.), set )
import qualified Control.Monad.Reader as CMR
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.TraversableFC ( anyFC )
import           GHC.TypeNats ( KnownNat, type (<=) )
import           Numeric (showHex)

import qualified Data.Macaw.Architecture.Info as DMAI
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.BinaryLoader.ELF as DMBE
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

import qualified Ambient.Extensions as AExt
import qualified Ambient.Lift as AL
import qualified Ambient.Loader.BinaryConfig as ALB
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
                 -> ALB.LoadedBinaryPath arch binFmt
                 -- ^ Binary to disassemble
                 -> LCF.HandleAllocator
                 -> DMS.GenArchVals mem arch
                 -> sym
                 -> LCSEv.ExecutionFeature p sym ext rtp
wmeReturnFeature archInfo loadedBinaryPath hdlAlloc archVals sym = LCSEv.ExecutionFeature $ \estate -> do
  let symArchFns = DMS.archFunctions archVals
  let regsRepr = LCT.StructRepr (DMS.crucArchRegTypes (DMS.archFunctions archVals))
  case estate of
    LCSE.ReturnState _fnName ctx regs state
      | Just PC.Refl <- PC.testEquality regsRepr (LCS.regType regs) ->
        case LCS.regValue (DMS.lookupReg archVals regs DMC.ip_reg) of
          LCLM.LLVMPointer _ ipVal -> do
            symNatAddr <- WI.bvToNat sym ipVal
            case WI.asNat symNatAddr of
              Just addr -> do
                mCfg <- buildCfgFromAddr archInfo loadedBinaryPath hdlAlloc (toInteger addr) symArchFns
                case mCfg of
                  Just (LCCC.SomeCFG cfg) -> do
                    let blockId = LCCC.cfgEntryBlockID cfg
                    let postdom = LCAP.postdomInfo cfg
                    let regMap = LCS.RegMap (Ctx.empty Ctx.:> regs)
                    let callFrame = LCSC.mkCallFrame cfg postdom regMap
                    let call = LCSE.CrucibleCall blockId callFrame
                    let tailCallState = LCSE.TailCallState ctx call state
                    return $ LCSEv.ExecutionFeatureNewState tailCallState
                  Nothing -> AP.panic AP.WME
                                      "wmeReturnFeature"
                                      [  "Failed to build CFG at address "
                                      ++ (show (WI.printSymExpr ipVal)) ]
              Nothing -> AP.panic AP.WME
                                  "wmeReturnFeature"
                                  [  "Encountered symbolic instruction pointer: "
                                  ++ (show (WI.printSymExpr ipVal)) ]
    _ -> return LCSEv.ExecutionFeatureNoChange

-- | Given an address and a binary, this function builds a CFG for the function
-- at the given address.  Returns 'Nothing' on failure.
buildCfgFromAddr :: forall arch binFmt w
                  . ( w ~ DMC.ArchAddrWidth arch
                    , DMB.BinaryLoader arch binFmt
                    , KnownNat w
                    , 1 <= w )
                 => DMAI.ArchitectureInfo arch
                 -> ALB.LoadedBinaryPath arch binFmt
                 -- ^ Binary to disassemble
                 -> LCF.HandleAllocator
                 -> Integer
                 -- ^ Address to disassemble from
                 -> DMS.MacawSymbolicArchFunctions arch
                 -> IO (Maybe (LCCC.SomeCFG (DMS.MacawExt arch)
                                            (Ctx.EmptyCtx Ctx.::> DMS.ArchRegStruct arch)
                                            (DMS.ArchRegStruct arch)))
buildCfgFromAddr archInfo loadedBinaryPath hdlAlloc addr symArchFns = do
  let mem = DMB.memoryImage $ ALB.lbpBinary loadedBinaryPath
  let symMap = ALB.lbpAddrSymMap loadedBinaryPath
  let mOff = DMBE.resolveAbsoluteAddress mem (fromInteger addr)
  case mOff of
    Just off -> do
      let discoveryState = DMD.cfgFromAddrs archInfo mem symMap [off] []
      someCfg <- lift ((discoveryState ^. DMD.funInfo) Map.! off)
      return (Just someCfg)
    Nothing -> return Nothing
  where
    -- Lift a disassembled function to a crucible CFG
    lift (Some fn) =
      AL.liftDiscoveredFunction hdlAlloc "weird-machine" symArchFns fn

-- | This function is used to look up a function handle when a call is
-- encountered within a weird machine.  Because 'wmeReturnFeature' flags all
-- ROP gadgets as ending in a tail call, this function is also called at the
-- end of each gadget to disassemble and jump to the next gadget.
wmeLookupFunction
  :: forall arch mem binFmt p sym bak solver scope st fs
   . ( bak ~ LCBO.OnlineBackend solver scope st fs
     , sym ~ WE.ExprBuilder scope st fs
     , p ~ AExt.AmbientSimulatorState sym arch
     , DMS.SymArchConstraints arch
     , LCB.IsSymBackend sym bak
     , WPO.OnlineSolver solver
     , DMB.BinaryLoader arch binFmt
     )
  => bak
  -> DMAI.ArchitectureInfo arch
  -> DMS.GenArchVals mem arch
  -> ALB.LoadedBinaryPath arch binFmt
  -> LCF.HandleAllocator
  -> DMS.LookupFunctionHandle p sym arch
wmeLookupFunction bak archInfo archVals loadedBinaryPath hdlAlloc =
  DMS.LookupFunctionHandle $ \state _mem regs -> do
    addr <- AVS.extractIP bak archVals regs
    mCfg <- buildCfgFromAddr archInfo loadedBinaryPath hdlAlloc (toInteger addr) symArchFns
    case mCfg of
      Just (LCCC.SomeCFG cfg) -> do
        let handle = LCCC.cfgHandle cfg
        let fnState = LCS.UseCFG cfg (LCAP.postdomInfo cfg)
        return (handle, AVS.insertFunctionHandle state handle fnState)
      Nothing -> AP.panic AP.WME
                          "wmeLookupFunction"
                          ["Failed to build CFG at 0x" ++ (showHex addr "")]
  where
    symArchFns = DMS.archFunctions archVals

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
wmExecutor :: forall arch binFmt w bak sym mem solver scope st fs
            . ( w ~ DMC.ArchAddrWidth arch
              , bak ~ LCBO.OnlineBackend solver scope st fs
              , sym ~ WE.ExprBuilder scope st fs
              , DMS.SymArchConstraints arch
              , 1 <= w
              , KnownNat w
              , LCB.IsSymInterface sym
              , DMB.BinaryLoader arch binFmt
              , WPO.OnlineSolver solver
              )
           => bak
           -> DMAI.ArchitectureInfo arch
           -> ALB.LoadedBinaryPath arch binFmt
           -- ^ Binary to disassemble
           -> LCF.HandleAllocator
           -> DMS.GenArchVals mem arch
           -> [LCS.GenericExecutionFeature sym]
           -- ^ Additional execution features to use when executing the weird
           -- machine
           -> AVW.WMMCallback arch sym
wmExecutor bak archInfo loadedBinaryPath hdlAlloc archVals execFeatures = AVW.WMMCallback $ \addr st -> do
  let sym = LCB.backendGetSym bak
  let symArchFns = DMS.archFunctions archVals
  let archInfo' = archInfo { DMAI.archClassifier = DMAI.archClassifier archInfo
                                               <|> weirdClassifier }
  let lookupFn = wmeLookupFunction bak archInfo' archVals loadedBinaryPath hdlAlloc
  mCfg <- buildCfgFromAddr archInfo' loadedBinaryPath hdlAlloc addr symArchFns
  case mCfg of
    Just (LCCC.SomeCFG cfg) -> do
      let ctx' = set (LCS.cruciblePersonality . AExt.overrideLookupFunctionHandle)
                     (Just lookupFn)
                     (st ^. LCS.stateContext)
      let globals = st ^. LCSE.stateGlobals
      let regsRepr = LCT.StructRepr (DMS.crucArchRegTypes symArchFns)
      case st ^. LCSE.stateTree . LCSE.actFrame . LCS.gpValue of
        LCSC.RF _ reg ->
          case PC.testEquality regsRepr (LCS.regType reg) of
            Just PC.Refl -> do
              let simAction = LCS.runOverrideSim regsRepr (LCS.regValue <$> LCS.callCFG cfg (LCS.RegMap (Ctx.empty Ctx.:> reg)))
              let st' = LCS.InitialState ctx' globals LCS.defaultAbortHandler regsRepr simAction
              let executionFeatures = (wmeReturnFeature archInfo' loadedBinaryPath hdlAlloc archVals sym) : fmap LCS.genericToExecutionFeature execFeatures
              res <- LCS.executeCrucible executionFeatures st'
              return $ AVW.WMMResultCompleted res
            _ -> AP.panic AP.WME "wmExecutor" ["Unexpected register shape"]

        -- NOTE: Because the executor returns 'WMMResultNoChange' for
        -- everything but 'RF' types, the executor only works for return
        -- oriented programs.  Adding a branch for 'MF' types is required to
        -- support call oriented weird machines.
        _ -> return AVW.WMMResultNoChange
    Nothing -> AP.panic AP.WME
                        "wmExecutor"
                        ["Failed to build CFG at 0x" ++ (showHex addr "")]
