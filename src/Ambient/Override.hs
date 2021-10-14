{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

module Ambient.Override ( buildArgumentRegisterAssignment ) where

import qualified Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Panic as AP

-- | Build an Assignment representing the arguments to a system call or
-- function argument from a list of registers
buildArgumentRegisterAssignment
  :: LCT.CtxRepr args
  -- ^ Types of arguments
  -> [LCS.RegEntry sym (LCLM.LLVMPointerType 64)]
  -- ^ List of argument registers
  -> Ctx.Assignment (LCS.RegEntry sym) args
  -- ^ Argument values
buildArgumentRegisterAssignment argTyps regEntries = go argTyps regEntries'
  where
    -- Drop unused registers from regEntries and reverse list to account for
    -- right-to-left processing when using 'Ctx.viewAssign'
    regEntries' = reverse (take (Ctx.sizeInt (Ctx.size argTyps)) regEntries)

    go :: LCT.CtxRepr args
       -> [LCS.RegEntry sym (LCLM.LLVMPointerType 64)]
       -> Ctx.Assignment (LCS.RegEntry sym) args
    go typs regs =
      case Ctx.viewAssign typs of
        Ctx.AssignEmpty -> Ctx.empty
        Ctx.AssignExtend typs' (LCLM.LLVMPointerRepr w) | Just WI.Refl <- WI.testEquality w (WI.knownNat @64) ->
          case regs of
            [] -> AP.panic AP.Override
                           "buildArgumentRegisterAssignment"
                           ["Override expects too many arguments"]
            reg : regs' ->
              (go typs' regs') Ctx.:> reg
        _ -> AP.panic AP.Override
                      "buildArgumentRegisterAssignment"
                      ["Currently only LLVMPointer arguments are supported"]
