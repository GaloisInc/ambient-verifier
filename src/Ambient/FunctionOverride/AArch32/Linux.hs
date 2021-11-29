{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module provides definitions to support the 32 bit Linux ABI for AArch32
--
-- See <https://github.com/ARM-software/abi-aa/releases> for details
module Ambient.FunctionOverride.AArch32.Linux (
  aarch32LinuxFunctionABI
  ) where

import qualified Data.Map as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN

import qualified Data.Macaw.AArch32.Symbolic as DMAS
import qualified Data.Macaw.ARM as DMA
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import qualified Data.Macaw.Symbolic as DMS
import qualified Language.ASL.Globals as ASL
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT

import qualified Ambient.FunctionOverride as AF
import qualified Ambient.Override as AO
import qualified Ambient.Panic as AP

-- | Integer arguments are passed in the first four registers in ARM
aarch32LinuxIntegerArgumentRegisters
  :: forall atps sym
    . LCT.CtxRepr atps
  -- ^ The argument types
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes DMA.ARM)
  -- ^ A register structure containing symbolic values
  -> Ctx.Assignment (LCS.RegEntry sym) atps
aarch32LinuxIntegerArgumentRegisters argTypes regFile =
  AO.buildArgumentRegisterAssignment ptrWidth argTypes regList
  where
    ptrWidth = PN.knownNat @32
    regList = map lookupReg [ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
                            , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")
                            , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")
                            , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")
                            ]
    lookupReg r = LCS.RegEntry (LCLM.LLVMPointerRepr ptrWidth)
                               (LCS.unRV (DMAS.lookupReg r regFile))

-- | Inject override return values back into the register state
--
-- Void returns ('LCT.UnitRepr') have no effect.
--
-- Otherwise, an integer return value is placed into r0
aarch32LinuxIntegerReturnRegisters
  :: LCT.TypeRepr tp
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym tp)
  -> LCS.RegValue sym (DMS.ArchRegStruct DMA.ARM)
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMA.ARM))
aarch32LinuxIntegerReturnRegisters ovTy ovSim initRegs =
  case ovTy of
    LCT.UnitRepr -> ovSim >> return initRegs
    LCLM.LLVMPointerRepr w
      | Just PC.Refl <- PC.testEquality w (PN.knownNat @32) -> do
          result <- ovSim
          let r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
          return $! DMAS.updateReg r0 (const (LCS.RV result)) initRegs
    _ -> AP.panic AP.FunctionOverride "aarch32LinuxIntegerReturnRegisters" [ "Unsupported return type: " ++ show ovTy ]

aarch32LinuxFunctionABI :: AF.BuildFunctionABI DMA.ARM sym p
aarch32LinuxFunctionABI = AF.BuildFunctionABI $ \_bumpEndVar _memVar ovs ->
  AF.FunctionABI { AF.functionIntegerArgumentRegisters = aarch32LinuxIntegerArgumentRegisters
                 , AF.functionIntegerReturnRegisters = aarch32LinuxIntegerReturnRegisters
                 , AF.functionNameMapping =
                     Map.fromList [ (AF.functionName fo, sfo)
                                  | sfo@(AF.SomeFunctionOverride fo) <- ovs
                                  ]
                 }
