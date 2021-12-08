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

import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )

import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.X86 as DMX
import qualified Data.Macaw.X86.Symbolic as DMXS
import qualified Data.Macaw.X86.X86Reg as DMXR
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Override as AO
import qualified Ambient.Panic as AP
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.Extension as AFE

-- | Extract integer arguments from x86_64 registers.
x86_64LinuxIntegerArgumentRegisters
  :: LCT.CtxRepr atps
  -- ^ Types of argument registers
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes DMX.X86_64)
  -- ^ Argument register values
  -> Ctx.Assignment (LCS.RegEntry sym) atps
x86_64LinuxIntegerArgumentRegisters argTypes regs =
  let regList = map lookupReg DMX.x86ArgumentRegs in
  AO.buildArgumentRegisterAssignment (PN.knownNat @64) argTypes regList
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
  :: LCT.TypeRepr t
  -- ^ Override return type
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym t)
  -- ^ OverrideSim action producing the override's return value
  -> LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64)
  -- ^ Argument register values from before override execution
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64))
x86_64LinuxIntegerReturnRegisters ovTyp ovSim initRegs =
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
    _ -> AP.panic AP.FunctionOverride
                  "x86_64LinuxIntegerReturnRegisters"
                  ["Unsupported override return type: " ++ show ovTyp]
    -- NOTE: If we encounter an override that returns a 128 bit int we'll
    -- need to add support for that here

x86_64LinuxFunctionABI :: AF.BuildFunctionABI DMX.X86_64 sym p
x86_64LinuxFunctionABI = AF.BuildFunctionABI $ \bumpEndVar memVar ovs kernelOvs ->
  -- Hacky overrides
  --
  -- TODO: Remove these (see #19)
  let ?recordLLVMAnnotation = \_ _ _ -> return () in
  let ?ptrWidth = PN.knownNat @64 in
  let hackyOverrides = [ AF.SomeFunctionOverride (AF.buildHackyBumpMallocOverride bumpEndVar)
                       , AF.SomeFunctionOverride (AF.buildHackyBumpCallocOverride bumpEndVar memVar)
                       ]
  in AF.FunctionABI { AF.functionIntegerArgumentRegisters = x86_64LinuxIntegerArgumentRegisters
                    , AF.functionIntegerReturnRegisters = x86_64LinuxIntegerReturnRegisters
                    , AF.functionNameMapping =
                      Map.fromList [ (AF.functionName fo, sfo)
                                   | sfo@(AF.SomeFunctionOverride fo) <- hackyOverrides ++ ovs
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
