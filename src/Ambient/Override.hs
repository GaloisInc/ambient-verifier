{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.Override
  ( buildArgumentRegisterAssignment
  , bvToPtr
  , ptrToBv32
  ) where

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           GHC.TypeNats ( type (<=), KnownNat )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Panic as AP

-- | Build an Assignment representing the arguments to a system call or
-- function argument from a list of registers
buildArgumentRegisterAssignment
  :: forall w args sym
    . PN.NatRepr w
  -- ^ Pointer width
  -> LCT.CtxRepr args
  -- ^ Types of arguments
  -> [LCS.RegEntry sym (LCLM.LLVMPointerType w)]
  -- ^ List of argument registers
  -> Ctx.Assignment (LCS.RegEntry sym) args
  -- ^ Argument values
buildArgumentRegisterAssignment ptrW argTyps regEntries = go argTyps regEntries'
  where
    -- Drop unused registers from regEntries and reverse list to account for
    -- right-to-left processing when using 'Ctx.viewAssign'
    regEntries' = reverse (take (Ctx.sizeInt (Ctx.size argTyps)) regEntries)

    go :: forall args'
        . LCT.CtxRepr args'
       -> [LCS.RegEntry sym (LCLM.LLVMPointerType w)]
       -> Ctx.Assignment (LCS.RegEntry sym) args'
    go typs regs =
      case Ctx.viewAssign typs of
        Ctx.AssignEmpty -> Ctx.empty
        Ctx.AssignExtend typs' (LCLM.LLVMPointerRepr w) | Just WI.Refl <- WI.testEquality w ptrW ->
          case regs of
            [] -> AP.panic AP.Override
                           "buildArgumentRegisterAssignment"
                           ["Override expects too many arguments"]
            reg : regs' ->
              (go typs' regs') Ctx.:> reg
        _ -> AP.panic AP.Override
                      "buildArgumentRegisterAssignment"
                      ["Currently only LLVMPointer arguments are supported"]

-- | Zero extend a bitvector to a 64-bit LLVMPointer
bvToPtr :: forall sym srcW ptrW
         . ( LCB.IsSymInterface sym
           , 1 <= srcW
           , KnownNat srcW
           )
           => sym
           -> WI.SymExpr sym (WI.BaseBVType srcW)
           -> PN.NatRepr ptrW
           -> IO (LCS.RegValue sym (LCLM.LLVMPointerType ptrW))
bvToPtr sym bv ptrW =
  case PN.compareNat (WI.knownNat @srcW) ptrW of
    PN.NatEQ -> LCLM.llvmPointer_bv sym bv
    PN.NatLT _w -> WI.bvZext sym ptrW bv >>= LCLM.llvmPointer_bv sym
    PN.NatGT _w -> AP.panic AP.Override "bvToPtr" ["Bitvector is larger than pointer width and cannot be extended: " ++ show (WI.knownNat @srcW)]

-- | Convert a 64-bit LLVMPointer to a 32-bit vector by dropping the upper 32
-- bits
ptrToBv32 :: ( LCB.IsSymInterface sym )
          => sym
          -> PN.NatRepr w
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -> IO (LCS.RegEntry sym (LCT.BVType 32))
ptrToBv32 sym nr ptr = do
  bvW <- LCLM.projectLLVM_bv sym (LCS.regValue ptr)
  case PN.compareNat nr (WI.knownNat @32) of
    PN.NatLT _ -> AP.panic AP.Override "ptrToBv32" ["Pointer too small to truncate to 32 bits: " ++ show nr]
    PN.NatEQ -> return $! LCS.RegEntry LCT.knownRepr bvW
    PN.NatGT _w -> do
      lower <- WI.bvTrunc sym (WI.knownNat @32) bvW
      return $! LCS.RegEntry LCT.knownRepr lower
