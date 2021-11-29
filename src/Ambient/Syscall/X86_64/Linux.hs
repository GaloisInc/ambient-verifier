{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.Syscall.X86_64.Linux ( x86_64LinuxSyscallABI ) where

import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Types as DMT
import qualified Data.Macaw.X86 as DMX
import qualified Data.Macaw.X86.X86Reg as DMXR
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Override as AO
import qualified Ambient.Panic as AP
import qualified Ambient.Syscall as AS

-- | Extract syscall arguments from x86_64 registers.  See documentation on
-- 'syscallArgumentRegisters for more info.
x86_64LinuxSyscallArgumentRegisters :: forall sym args atps
   . ( LCB.IsSymInterface sym )
  => LCT.CtxRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> LCT.CtxRepr args
  -> Ctx.Assignment (LCS.RegEntry sym) args
x86_64LinuxSyscallArgumentRegisters regTyps regs syscallTyps =
  case (LCS.regValue regs) of
    Ctx.Empty Ctx.:> _
              Ctx.:> rdi
              Ctx.:> rsi
              Ctx.:> rdx
              Ctx.:> r10
              Ctx.:> r8
              Ctx.:> r9 -> do
      case regTyps of
        Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr _
                  Ctx.:> LCLM.LLVMPointerRepr wrdi
                  Ctx.:> LCLM.LLVMPointerRepr wrsi
                  Ctx.:> LCLM.LLVMPointerRepr wrdx
                  Ctx.:> LCLM.LLVMPointerRepr wr10
                  Ctx.:> LCLM.LLVMPointerRepr wr8
                  Ctx.:> LCLM.LLVMPointerRepr wr9
                  | Just WI.Refl <- WI.testEquality wrdi (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wrsi (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wrdx (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wr10 (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wr8 (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wr9 (WI.knownNat @64) ->
          -- Extract argument registers and put in list.
          let regEntries = map toRegEntry [rdi, rsi, rdx, r10, r8, r9] in
          -- Build an assignment from 'regEntries'
          AO.buildArgumentRegisterAssignment (PN.knownNat @64) syscallTyps regEntries
        _ -> AP.panic AP.Syscall
                      "x86_64LinuxSyscallArgumentRegisters"
                      ["Unexpected argument register types"]
    _ -> AP.panic AP.Syscall
                  "x86_64LinuxSyscallArgumentRegisters"
                  ["Unexpected argument register shape"]
  where
    toRegEntry :: LCS.RegValue' sym (LCLM.LLVMPointerType 64)
               -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
    toRegEntry x = (LCS.RegEntry (LCLM.LLVMPointerRepr (WI.knownNat @64)) (LCS.unRV x))

-- | Extract syscall number from x86_64 registers.  See documentation on
-- 'syscallNumberRegister' for more info.
x86_64LinuxSyscallNumberRegister :: forall sym w atps
   . ( LCB.IsSymInterface sym
     , DMC.RegAddrWidth (DMC.ArchReg DMX.X86_64) ~ w )
  => sym
  -> Ctx.Assignment LCT.TypeRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> IO (LCS.RegEntry sym (LCT.BVType w))
x86_64LinuxSyscallNumberRegister sym typs regs = do
  bv <- LCLM.projectLLVM_bv sym (LCS.unRV (x86_64LinuxGetReg typs regs DMX.RAX))
  return LCS.RegEntry { LCS.regType = LCT.BVRepr WI.knownNat
                      , LCS.regValue = bv }

-- | Assemble x86_64 return register state from syscall return value.  See
-- documentation for 'syscallReturnRegisters' for more info.
x86_64LinuxSyscallReturnRegisters
  :: LCT.TypeRepr t
  -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym t)
  -> LCT.CtxRepr atps
  -> LCS.RegEntry sym (LCT.StructType atps)
  -> LCT.CtxRepr rtps
  -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym (LCT.StructType rtps))
x86_64LinuxSyscallReturnRegisters ovTyp ovSim atps argRegs rtps =
  case rtps of
    Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr wrax
              Ctx.:> LCLM.LLVMPointerRepr wrdx
              | Just WI.Refl <- WI.testEquality wrax (WI.knownNat @64)
              , Just WI.Refl <- WI.testEquality wrdx (WI.knownNat @64) ->
      case ovTyp of
        LCT.UnitRepr -> do
          ovSim
          let rax = x86_64LinuxGetReg atps argRegs DMXR.RAX
          let rdx = x86_64LinuxGetReg atps argRegs DMXR.RDX
          return (Ctx.empty Ctx.:> rax Ctx.:> rdx)
        LCLM.LLVMPointerRepr w
          | Just WI.Refl <- WI.testEquality w (WI.knownNat @64) -> do
          result <- ovSim
          let rdx = x86_64LinuxGetReg atps argRegs DMXR.RDX
          return (Ctx.empty Ctx.:> (LCS.RV result) Ctx.:> rdx)
        _ -> AP.panic AP.Syscall
                      "x86_64LinuxSyscallReturnRegisters"
                      ["Unsupported override return type"]
        -- NOTE: Fill in return types as needed for new syscall overrides
        -- here
    _ -> AP.panic AP.Syscall
                  "x86_64LinuxSyscallReturnRegisters"
                  ["Unexpected shape of return registers"]

-- | An ABI for Linux syscalls on x86_64 processors
x86_64LinuxSyscallABI :: AS.BuildSyscallABI DMX.X86_64 sym p
x86_64LinuxSyscallABI = AS.BuildSyscallABI $ \fs memVar properties ->
  AS.SyscallABI { AS.syscallArgumentRegisters = x86_64LinuxSyscallArgumentRegisters
                , AS.syscallNumberRegister = x86_64LinuxSyscallNumberRegister
                , AS.syscallReturnRegisters = x86_64LinuxSyscallReturnRegisters
                , AS.syscallMapping = Map.fromList
                    [ (0, AS.SomeSyscall (AS.buildReadOverride ptrW fs memVar))
                    , (1, AS.SomeSyscall (AS.buildWriteOverride ptrW fs memVar))
                    , (2, AS.SomeSyscall (AS.buildOpenOverride ptrW fs memVar))
                    , (3, AS.SomeSyscall (AS.buildCloseOverride ptrW fs memVar))
                    , (59, AS.SomeSyscall (AS.buildExecveOverride properties ptrW))
                    , (60, AS.SomeSyscall (AS.exitOverride ptrW))
                    , (110, AS.SomeSyscall (AS.getppidOverride ptrW))
                    ]
                }
  where
    ptrW = PN.knownNat @64

-- | Extract the value of a given register from the x86_64 argument register
-- state
x86_64LinuxGetReg :: Ctx.Assignment LCT.TypeRepr atps
                  -- ^ Types of argument registers
                  -> LCS.RegEntry sym (LCT.StructType atps)
                  -- ^ Argument register state
                  -> DMXR.X86Reg (DMT.BVType 64)
                  -- ^ Register to extract the value from
                  -> LCS.RegValue' sym (LCLM.LLVMPointerType 64)
x86_64LinuxGetReg atps regs reg =
  case (LCS.regValue regs) of
    Ctx.Empty Ctx.:> rax
              Ctx.:> rdi
              Ctx.:> rsi
              Ctx.:> rdx
              Ctx.:> r10
              Ctx.:> r8
              Ctx.:> r9 -> do
      case atps of
        Ctx.Empty Ctx.:> LCLM.LLVMPointerRepr wrax
                  Ctx.:> LCLM.LLVMPointerRepr wrdi
                  Ctx.:> LCLM.LLVMPointerRepr wrsi
                  Ctx.:> LCLM.LLVMPointerRepr wrdx
                  Ctx.:> LCLM.LLVMPointerRepr wr10
                  Ctx.:> LCLM.LLVMPointerRepr wr8
                  Ctx.:> LCLM.LLVMPointerRepr wr9
                  | Just WI.Refl <- WI.testEquality wrax (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wrdi (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wrsi (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wrdx (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wr10 (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wr8 (WI.knownNat @64)
                  , Just WI.Refl <- WI.testEquality wr9 (WI.knownNat @64) ->
          case reg of
            DMXR.RAX -> rax
            DMXR.RDI -> rdi
            DMXR.RSI -> rsi
            DMXR.RDX -> rdx
            DMXR.R10 -> r10
            DMXR.R8  -> r8
            DMXR.R9  -> r9
            _ -> AP.panic AP.Syscall
                         "x86_64LinuxGetReg"
                         ["Unexpected argument register: " ++ (show reg)]
        _ -> AP.panic AP.Syscall
                      "x86_64LinuxGetReg"
                      ["Unexpected argument register types"]
    _ -> AP.panic AP.Syscall
                  "x86_64LinuxGetReg"
                  ["Unexpected argument register shape"]
