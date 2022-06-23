{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.Override
  ( buildArgumentAssignment
  , narrowPointerType
  , extendPointerType
  , bvToPtr
  , ptrToBv8
  , ptrToBv32
  , overrideMemOptions
  ) where

import qualified Control.Monad.Catch as CMC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import           GHC.TypeNats ( type (<=), KnownNat )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Exception as AE
import qualified Ambient.Panic as AP

-- | Build an Assignment representing the arguments to a system call or
-- function argument from a list of arguments. For system calls, this list will
-- consist solely of register arguments. For function calls, the beginning of
-- the list will consist of register arguments, but if the function has
-- sufficiently many arguments, the rest of the list will contain arguments
-- from the stack. See @Note [Passing arguments to functions]@ in
-- "Ambient.FunctionOverride".
buildArgumentAssignment
  :: forall w args sym bak
   . (1 <= w, KnownNat w, LCB.IsSymBackend sym bak)
  => bak
  -> LCT.CtxRepr args
  -- ^ Types of arguments
  -> [LCS.RegEntry sym (LCLM.LLVMPointerType w)]
  -- ^ List of argument values
  -> IO (Ctx.Assignment (LCS.RegEntry sym) args)
  -- ^ Argument values
buildArgumentAssignment bak argTyps argEntries = go argTyps argEntries'
  where
    -- Drop unused arguments from argEntries and reverse list to account for
    -- right-to-left processing when using 'Ctx.viewAssign'
    argEntries' = reverse (take (Ctx.sizeInt (Ctx.size argTyps)) argEntries)

    go :: forall args'
        . LCT.CtxRepr args'
       -> [LCS.RegEntry sym (LCLM.LLVMPointerType w)]
       -> IO (Ctx.Assignment (LCS.RegEntry sym) args')
    go typs args =
      case args of
        [] ->
          case Ctx.viewAssign typs of
            Ctx.AssignEmpty -> return Ctx.empty
            _ -> AP.panic AP.Override
                          "buildArgumentRegisterAssignment"
                          ["Override expects too many arguments"]
        arg : args' ->
          case Ctx.viewAssign typs of
            Ctx.AssignEmpty -> return Ctx.empty
            Ctx.AssignExtend typs' trep -> do
              arg' <- narrowPointerType bak trep arg
              rest <- go typs' args'
              return (rest Ctx.:> arg')

-- | Bitvector conversion from a wide width to a more narrow type.
newtype BvNarrowing sym w tp where
  BvNarrowing :: (LCS.RegEntry sym (LCLM.LLVMPointerType w) -> IO (LCS.RegEntry sym tp))
               -> BvNarrowing sym w tp

-- | Convert a @wideTp@ to a @narrowTp@. If both types are
-- 'LCLM.LLVMPointerType's, truncate the wider type to the narrow type.
-- Otherwise, require the types to be the same.
narrowPointerType ::
  forall sym bak wideTp narrowTp.
  LCB.IsSymBackend sym bak =>
  bak ->
  LCT.TypeRepr narrowTp ->
  LCS.RegEntry sym wideTp ->
  IO (LCS.RegEntry sym narrowTp)
narrowPointerType bak narrowTypeRepr wideEntry
  | LCLM.LLVMPointerRepr widePtrW <- LCS.regType wideEntry
  = case MapF.lookup narrowTypeRepr (conversions widePtrW) of
      Nothing -> CMC.throwM $ AE.FunctionTypeBvNarrowingError widePtrW
      Just (BvNarrowing toRegWidth) -> toRegWidth wideEntry

  | otherwise
  = case WI.testEquality (LCS.regType wideEntry) narrowTypeRepr of
      Just WI.Refl -> pure wideEntry
      Nothing -> CMC.throwM AE.FunctionTypeMismatch
  where
    -- Mapping of bitvector conversions to a narrow types. The wider-sized
    -- bitvector with width @widePtrW@ should always be the last element in the
    -- 'MapF.fromList' list to ensure that wide-width bitvectors do not undergo
    -- any conversion.
    conversions :: forall widePtrW.
                   (1 <= widePtrW) =>
                   PN.NatRepr widePtrW ->
                   MapF.MapF LCT.TypeRepr (BvNarrowing sym widePtrW)
    conversions widePtrW =
      MapF.fromList [ MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @8)) (BvNarrowing (bvTrunc (WI.knownNat @8)))
                    , MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @32)) (BvNarrowing (bvTrunc (WI.knownNat @32)))
                    , MapF.Pair (LCLM.LLVMPointerRepr widePtrW) (BvNarrowing return)
                    ]

    -- Truncate a bitvector down to @narrowPtrW@ bits.
    bvTrunc :: forall widePtrW narrowPtrW
             . (1 <= widePtrW, 1 <= narrowPtrW)
            => PN.NatRepr narrowPtrW
            -> LCS.RegEntry sym (LCLM.LLVMPointerType widePtrW)
            -> IO (LCS.RegEntry sym (LCLM.LLVMPointerType narrowPtrW))
    bvTrunc bvW ptr = adjustPtrEntrySize bak ptr bvW

-- | Bitvector conversion from a narrow type to a wider width.
-- Like 'BvConversion', except with the argument and result types in the
-- function reversed.
newtype BvExtension sym w tp where
  BvExtension :: (LCS.RegEntry sym tp -> IO (LCS.RegEntry sym (LCLM.LLVMPointerType w)))
              -> BvExtension sym w tp

-- | Convert a @narrowTp@ to a @wideTp@. If both types are
-- 'LCLM.LLVMPointerType's, zero-extend the narrow type to the wider type.
-- Otherwise, require the types to be the same.
extendPointerType ::
  forall sym bak narrowTp wideTp.
  LCB.IsSymBackend sym bak =>
  bak ->
  LCT.TypeRepr wideTp ->
  LCS.RegEntry sym narrowTp ->
  IO (LCS.RegEntry sym wideTp)
extendPointerType bak wideTypeRepr narrowEntry
  | LCLM.LLVMPointerRepr widePtrW <- wideTypeRepr
  = case MapF.lookup narrowTypeRepr (conversions widePtrW) of
      Nothing -> CMC.throwM $ AE.FunctionTypeBvExtensionError widePtrW
      Just (BvExtension toRegWidth) -> toRegWidth narrowEntry

  | otherwise
  = case WI.testEquality narrowTypeRepr wideTypeRepr of
      Just WI.Refl -> pure narrowEntry
      Nothing -> CMC.throwM AE.FunctionTypeMismatch
  where
    narrowTypeRepr = LCS.regType narrowEntry

    -- Mapping of conversions from narrow-width bitvectors to the wider width.
    -- The wider-sized bitvector with width @widePtrW@ should always be the
    -- last element in the 'MapF.fromList' list to ensure that wide-width
    -- bitvectors do not undergo any conversion.
    conversions :: forall widePtrW.
                   (1 <= widePtrW) =>
                   PN.NatRepr widePtrW ->
                   MapF.MapF LCT.TypeRepr (BvExtension sym widePtrW)
    conversions widePtrW =
      MapF.fromList [ MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @8)) (BvExtension (bvZext widePtrW))
                    , MapF.Pair (LCLM.LLVMPointerRepr (WI.knownNat @32)) (BvExtension (bvZext widePtrW))
                    , MapF.Pair (LCLM.LLVMPointerRepr widePtrW) (BvExtension return)
                    ]

    -- Zero-extend a bitvector to @widePtrW@ bits.
    bvZext :: forall narrowPtrW widePtrW
             . (1 <= narrowPtrW, 1 <= widePtrW)
            => PN.NatRepr widePtrW
            -> LCS.RegEntry sym (LCLM.LLVMPointerType narrowPtrW)
            -> IO (LCS.RegEntry sym (LCLM.LLVMPointerType widePtrW))
    bvZext bvW ptr = adjustPtrEntrySize bak ptr bvW

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

-- | Zero extend or truncate an 'LCLM.LLVMPointer' 'LCS.RegEntry'.
adjustPtrEntrySize ::
  forall sym bak srcW dstW.
  ( LCB.IsSymBackend sym bak
  , 1 <= srcW
  , 1 <= dstW
  ) =>
  bak ->
  LCS.RegEntry sym (LCLM.LLVMPointerType srcW) ->
  PN.NatRepr dstW ->
  IO (LCS.RegEntry sym (LCLM.LLVMPointerType dstW))
adjustPtrEntrySize bak srcPtr dstW = do
  let sym = LCB.backendGetSym bak
  bv <- LCLM.projectLLVM_bv bak $ LCS.regValue srcPtr
  rv <- bvToPtr sym bv dstW
  pure $ LCS.RegEntry (LCLM.LLVMPointerRepr dstW) rv

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
