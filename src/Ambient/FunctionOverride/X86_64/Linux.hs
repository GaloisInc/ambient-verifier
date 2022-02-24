{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.FunctionOverride.X86_64.Linux (
    x86_64LinuxIntegerArgumentRegisters
  , x86_64LinuxIntegerReturnRegisters
  , x86_64LinuxFunctionABI
  , x86_64LinuxTypes
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           GHC.TypeNats ( type (<=), KnownNat )

import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.X86 as DMX
import qualified Data.Macaw.X86.Symbolic as DMXS
import qualified Data.Macaw.X86.X86Reg as DMXR
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Extensions as AE
import qualified Ambient.Override as AO
import qualified Ambient.Panic as AP
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.Extension as AFE
import qualified Ambient.FunctionOverride.Overrides as AFO

-- | Extract integer arguments from x86_64 registers.
x86_64LinuxIntegerArgumentRegisters
  :: (LCB.IsSymBackend sym bak)
  => bak
  -> LCT.CtxRepr atps
  -- ^ Types of argument registers
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes DMX.X86_64)
  -- ^ Argument register values
  -> IO (Ctx.Assignment (LCS.RegEntry sym) atps)
x86_64LinuxIntegerArgumentRegisters bak argTypes regs =
  let regList = map lookupReg DMX.x86ArgumentRegs in
  AO.buildArgumentRegisterAssignment bak (PN.knownNat @64) argTypes regList
  where
    lookupReg r =
      case DMXS.lookupX86Reg r regs of
        Just v -> (LCS.RegEntry (LCLM.LLVMPointerRepr (WI.knownNat @64))
                                (LCS.unRV v))
        Nothing -> AP.panic AP.FunctionOverride
                            "x86_64LinuxIntegerArgumentRegisters"
                            ["Failed to lookup register: " ++ (show r)]

-- | Assemble x86_64 integer return register state from override return value.
x86_64LinuxIntegerReturnRegisters
  :: forall p sym bak ext r args rtp t
   . ( LCB.IsSymBackend sym bak )
  => bak
  -> LCT.TypeRepr t
  -- ^ Override return type
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym t)
  -- ^ OverrideSim action producing the override's return value
  -> LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64)
  -- ^ Argument register values from before override execution
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64))
x86_64LinuxIntegerReturnRegisters bak ovTyp ovSim initRegs =
  case ovTyp of
    LCT.UnitRepr -> do
      ovSim
      return initRegs
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @64) -> do
      result <- ovSim
      let mRegs = DMXS.updateX86Reg DMXR.RAX (\_ -> (LCS.RV result)) initRegs
      case mRegs of
        Just regs -> return regs
        Nothing -> AP.panic AP.FunctionOverride
                            "x86_64LinuxIntegerReturnRegisters"
                            ["Failed to update rax register"]
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @8) -> bvZext ovSim
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @32) -> bvZext ovSim
    _ -> AP.panic AP.FunctionOverride
                  "x86_64LinuxIntegerReturnRegisters"
                  ["Unsupported override return type: " ++ show ovTyp]
    -- NOTE: If we encounter an override that returns a 128 bit int we'll
    -- need to add support for that here
  where
    sym = LCB.backendGetSym bak

    -- | Zero extend an LLMVPointer in region 0 (a bitvector) to fit in an
    -- integer register
    bvZext
      :: (1 <= srcW, KnownNat srcW)
      => LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (LCLM.LLVMPointerType srcW))
      -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64))
    bvZext ov = do
      result <- ov
      asBv <- liftIO $ LCLM.projectLLVM_bv bak result
      asPtr <- liftIO $ AO.bvToPtr sym asBv (WI.knownNat @64)
      let mRegs = DMXS.updateX86Reg DMXR.RAX (\_ -> (LCS.RV asPtr)) initRegs
      case mRegs of
        Just regs -> return regs
        Nothing -> AP.panic AP.FunctionOverride
                            "x86_64LinuxIntegerReturnRegisters"
                            ["Failed to update rax register"]

x86_64LinuxFunctionABI :: AF.BuildFunctionABI DMX.X86_64 sym (AE.AmbientSimulatorState DMX.X86_64)
x86_64LinuxFunctionABI = AF.BuildFunctionABI $ \fs bumpEndVar memVar ovs kernelOvs ->
  let ?recordLLVMAnnotation = \_ _ _ -> return () in
  let ?ptrWidth = PN.knownNat @64 in
  let memOverrides = [ AF.SomeFunctionOverride (AFO.buildMemcpyOverride memVar)
                     , AF.SomeFunctionOverride (AFO.buildMemsetOverride memVar)
                     ] in
  -- Hacky overrides
  --
  -- TODO: Remove these (see #19)
  let hackyOverrides = [ AF.SomeFunctionOverride (AFO.buildHackyBumpMallocOverride bumpEndVar)
                       , AF.SomeFunctionOverride (AFO.buildHackyBumpCallocOverride bumpEndVar memVar)
                       ]
  in AF.FunctionABI { AF.functionIntegerArgumentRegisters = x86_64LinuxIntegerArgumentRegisters
                    , AF.functionIntegerReturnRegisters = x86_64LinuxIntegerReturnRegisters
                    , AF.functionNameMapping =
                      Map.fromList [ (AF.functionName fo, sfo)
                                   | sfo@(AF.SomeFunctionOverride fo) <-
                                       memOverrides ++ hackyOverrides ++
                                       AFO.networkOverrides fs memVar ++ ovs
                                   ]
                    , AF.functionKernelAddrMapping = kernelOvs
                    }

-- | A lookup function from 'AFE.TypeAlias' to types with the appropriate width
-- on X86_64 Linux.
x86_64LinuxTypes :: AFE.TypeLookup
x86_64LinuxTypes = AFE.TypeLookup $ \tp ->
  case tp of
    AFE.Byte -> Some (LCT.BVRepr (PN.knownNat @8))
    AFE.Int -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Long -> Some (LCT.BVRepr (PN.knownNat @64))
    AFE.PidT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Pointer -> Some (LCLM.LLVMPointerRepr (PN.knownNat @64))
    AFE.SizeT -> Some (LCT.BVRepr (PN.knownNat @64))
    AFE.UidT -> Some (LCT.BVRepr (PN.knownNat @32))
