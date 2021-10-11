{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.Verifier.WME (wmExecutor) where

import           Control.Lens ( (^.) )
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import           GHC.TypeNats ( KnownNat, type (<=) )
import           Numeric (showHex)

import qualified Data.Macaw.Architecture.Info as DMAI
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.CallFrame as LCSC
import qualified Lang.Crucible.Simulator.EvalStmt as LCSEv
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Discovery as AD
import qualified Ambient.Lift as AL
import qualified Ambient.Panic as AP
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
                 -> DMB.LoadedBinary arch binFmt
                 -- ^ Binary to disassemble
                 -> LCF.HandleAllocator
                 -> DMS.GenArchVals DMS.LLVMMemory arch
                 -> sym
                 -> LCSEv.ExecutionFeature p sym ext rtp
wmeReturnFeature archInfo loadedBinary hdlAlloc archVals sym = LCSEv.ExecutionFeature $ \estate -> do
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
                mCfg <- buildCfgFromAddr archInfo loadedBinary hdlAlloc (toInteger addr) symArchFns
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
                 -> DMB.LoadedBinary arch binFmt
                 -- ^ Binary to disassemble
                 -> LCF.HandleAllocator
                 -> Integer
                 -- ^ Address to disassemble from
                 -> DMS.MacawSymbolicArchFunctions arch
                 -> IO (Maybe (LCCC.SomeCFG (DMS.MacawExt arch)
                                            (Ctx.EmptyCtx Ctx.::> DMS.ArchRegStruct arch)
                                            (DMS.ArchRegStruct arch)))
buildCfgFromAddr archInfo loadedBinary hdlAlloc addr symArchFns = do
  let mem = DMB.memoryImage loadedBinary
  let symMap = AD.symbolMap loadedBinary
  let bvAddr :: forall ids. DMC.Value arch ids (DMT.BVType (DMC.RegAddrWidth (DMC.ArchReg arch)))
      bvAddr = DMC.CValue (DMC.BVCValue (WI.knownNat @(DMC.ArchAddrWidth arch)) addr)
  let mOff = DMC.valueAsSegmentOff mem bvAddr
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

-- | Produces a 'WMMCallback' for symbolically executing weird machines.  This
-- callback disassembles from the entry point of the weird machine, constructs
-- a crucible CFG, and then symbolically executes the CFG.
--
-- Currently this only supports return oriented programs, but could be extended
-- to support other types of weird machines.
wmExecutor :: forall arch binFmt w sym
            . ( w ~ DMC.ArchAddrWidth arch
              , DMS.SymArchConstraints arch
              , 1 <= w
              , KnownNat w
              , LCB.IsSymInterface sym
              , DMB.BinaryLoader arch binFmt )
           => DMAI.ArchitectureInfo arch
           -> DMB.LoadedBinary arch binFmt
           -- ^ Binary to disassemble
           -> LCF.HandleAllocator
           -> DMS.GenArchVals DMS.LLVMMemory arch
           -> [LCS.GenericExecutionFeature sym]
           -- ^ Additional execution features to use when executing the weird
           -- machine
           -> sym
           -> AVW.WMMCallback arch sym
wmExecutor archInfo loadedBinary hdlAlloc archVals execFeatures sym = AVW.WMMCallback $ \addr st -> do
  let symArchFns = DMS.archFunctions archVals
  mCfg <- buildCfgFromAddr archInfo loadedBinary hdlAlloc addr symArchFns
  case mCfg of
    Just (LCCC.SomeCFG cfg) -> do
      let ctx = st ^. LCS.stateContext
      let globals = st ^. LCSE.stateGlobals
      let regsRepr = LCT.StructRepr (DMS.crucArchRegTypes symArchFns)
      case st ^. LCSE.stateTree . LCSE.actFrame . LCS.gpValue of
        LCSC.RF _ reg ->
          case PC.testEquality regsRepr (LCS.regType reg) of
            Just PC.Refl -> do
              let simAction = LCS.runOverrideSim regsRepr (LCS.regValue <$> LCS.callCFG cfg (LCS.RegMap (Ctx.empty Ctx.:> reg)))
              let st' = LCS.InitialState ctx globals LCS.defaultAbortHandler regsRepr simAction
              let executionFeatures = (wmeReturnFeature archInfo loadedBinary hdlAlloc archVals sym) : fmap LCS.genericToExecutionFeature execFeatures
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
