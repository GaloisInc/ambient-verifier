{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.Override
  ( buildArgumentRegisterAssignment
  , bvToPtr
  , ptrToBv8
  , ptrToBv32
  , overrideMemOptions
  ) where

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import           GHC.TypeNats ( type (<=), KnownNat )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Panic as AP

-- | Bitvector conversion from the full register width to a narrow type
newtype BvConversion sym w tp where
  BvConversion :: (LCS.RegEntry sym (LCLM.LLVMPointerType w) -> IO (LCS.RegEntry sym tp))
               -> BvConversion sym w tp

-- | Build an Assignment representing the arguments to a system call or
-- function argument from a list of registers
buildArgumentRegisterAssignment
  :: forall w args sym bak
   . (1 <= w, KnownNat w, LCB.IsSymBackend sym bak)
  => bak
  -> PN.NatRepr w
  -- ^ Pointer width
  -> LCT.CtxRepr args
  -- ^ Types of arguments
  -> [LCS.RegEntry sym (LCLM.LLVMPointerType w)]
  -- ^ List of argument registers
  -> IO (Ctx.Assignment (LCS.RegEntry sym) args)
  -- ^ Argument values
buildArgumentRegisterAssignment bak ptrW argTyps regEntries = go argTyps regEntries'
  where
    sym = LCB.backendGetSym bak

    -- Drop unused registers from regEntries and reverse list to account for
    -- right-to-left processing when using 'Ctx.viewAssign'
    regEntries' = reverse (take (Ctx.sizeInt (Ctx.size argTyps)) regEntries)

    go :: forall args'
        . LCT.CtxRepr args'
       -> [LCS.RegEntry sym (LCLM.LLVMPointerType w)]
       -> IO (Ctx.Assignment (LCS.RegEntry sym) args')
    go typs regs =
      case regs of
        [] ->
          case Ctx.viewAssign typs of
            Ctx.AssignEmpty -> return Ctx.empty
            _ -> AP.panic AP.Override
                          "buildArgumentRegisterAssignment"
                          ["Override expects too many arguments"]
        reg : regs' ->
          case Ctx.viewAssign typs of
            Ctx.AssignEmpty -> return Ctx.empty
            Ctx.AssignExtend typs' trep
              | Just (BvConversion toRegWidth) <- MapF.lookup trep conversions -> do
                reg' <- toRegWidth reg
                rest <- go typs' regs'
                return (rest Ctx.:> reg')
            _ -> AP.panic AP.Override
                          "buildArgumentRegisterAssignment"
                          ["Currently only LLVMPointer arguments are supported"]

    -- Mapping of conversions from register width bitvectors to a narrow type.
    -- The register sized bitvector with width 'ptrW' should always be the last
    -- element in the 'MapF.fromList' list to ensure that register width
    -- bitvectors do not undergo any conversion.
    conversions :: MapF.MapF LCT.TypeRepr (BvConversion sym w)
    conversions =
      MapF.fromList [ MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @8)) (BvConversion (bvTrunc WI.knownNat))
                    , MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @32)) (BvConversion (bvTrunc WI.knownNat))
                    , MapF.Pair (LCLM.LLVMPointerRepr ptrW) (BvConversion return)
                    ]

    -- Truncate a bitvector down to 'bvW' bits.
    bvTrunc :: (1 <= bvW, KnownNat bvW)
            => PN.NatRepr bvW
            -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
            -> IO (LCS.RegEntry sym (LCLM.LLVMPointerType bvW))
    bvTrunc bvW ptr = do
      bv <- LCLM.projectLLVM_bv bak (LCS.regValue ptr)
      rv <- bvToPtr sym bv bvW
      return (LCS.RegEntry (LCLM.LLVMPointerRepr bvW) rv)

-- | Zero extend or truncate bitvector to an LLVMPointer
bvToPtr :: forall sym srcW ptrW
         . ( LCB.IsSymInterface sym
           , 1 <= srcW
           , 1 <= ptrW
           )
           => sym
           -> WI.SymExpr sym (WI.BaseBVType srcW)
           -> PN.NatRepr ptrW
           -> IO (LCS.RegValue sym (LCLM.LLVMPointerType ptrW))
bvToPtr sym bv ptrW =
  case PN.compareNat srcW ptrW of
    PN.NatEQ -> LCLM.llvmPointer_bv sym bv
    PN.NatLT _w -> WI.bvZext sym ptrW bv >>= LCLM.llvmPointer_bv sym
    PN.NatGT _w -> WI.bvTrunc sym ptrW bv >>= LCLM.llvmPointer_bv sym
  where
    srcW :: PN.NatRepr srcW
    srcW = case WI.exprType bv of
             WI.BaseBVRepr w -> w

-- | Convert an 'LCLM.LLVMPtr' to an 8-bit vector by dropping the upper bits.
ptrToBv8 :: ( LCB.IsSymBackend sym bak )
          => bak
          -> PN.NatRepr w
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -> IO (LCS.RegEntry sym (LCT.BVType 8))
ptrToBv8 = ptrToBv

-- | Convert an 'LCLM.LLVMPtr' to a 32-bit vector by dropping the upper bits.
ptrToBv32 :: ( LCB.IsSymBackend sym bak )
          => bak
          -> PN.NatRepr w
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -> IO (LCS.RegEntry sym (LCT.BVType 32))
ptrToBv32 = ptrToBv

-- | Convert an 'LCLM.LLVMPtr' to a bitvector by dropping the upper bits.
ptrToBv :: forall sym bak ptrW destW
         . ( LCB.IsSymBackend sym bak
           , KnownNat destW
           , 1 <= destW
           )
        => bak
        -> PN.NatRepr ptrW
        -> LCS.RegEntry sym (LCLM.LLVMPointerType ptrW)
        -> IO (LCS.RegEntry sym (LCT.BVType destW))
ptrToBv bak nr ptr = do
  let sym = LCB.backendGetSym bak
  bvW <- LCLM.projectLLVM_bv bak (LCS.regValue ptr)
  case PN.compareNat nr (WI.knownNat @destW) of
    PN.NatLT _ -> AP.panic AP.Override "ptrToBv32" ["Pointer too small to truncate to 32 bits: " ++ show nr]
    PN.NatEQ -> return $! LCS.RegEntry LCT.knownRepr bvW
    PN.NatGT _w -> do
      lower <- WI.bvTrunc sym (WI.knownNat @destW) bvW
      return $! LCS.RegEntry LCT.knownRepr lower

-- | The memory options used to configure the memory model for system call and
-- function overrides.
--
-- We use the most lax memory options possible, as machine code breaks many of
-- the C-level rules.
overrideMemOptions :: LCLM.MemOptions
overrideMemOptions = LCLM.laxPointerMemOptions
