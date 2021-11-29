{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Ambient.FunctionOverride (
    FunctionOverride(..)
  , SomeFunctionOverride(..)
  , FunctionABI(..)
  , BuildFunctionABI(..)
    -- * Overrides
  , buildMallocOverride
  , buildCallocOverride
    -- * Hacky overrides
  , hackyFreeOverride
  , hackyGdErrorExOverride
  , hackyPrintfOverride
  , buildHackyBumpMallocOverride
  , buildHackyBumpCallocOverride
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI

import           Ambient.Override

-------------------------------------------------------------------------------
-- Function Call Overrides
-------------------------------------------------------------------------------

-- | FunctionOverride captures an override and type information about how to
-- call it
data FunctionOverride p sym args ext ret =
  FunctionOverride { functionName :: WF.FunctionName
                   -- ^ Name of the function
                   , functionArgTypes :: LCT.CtxRepr args
                   -- ^ Types of the arguments to the function
                   , functionReturnType :: LCT.TypeRepr ret
                   -- ^ Return type of the function
                   , functionOverride
                       :: (LCB.IsSymInterface sym)
                       => sym
                       -> Ctx.Assignment (LCS.RegEntry sym) args
                       -- Arguments to function
                       -> (forall rtp args' ret'. LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret))
                   -- ^ Override capturing behavior of the function
                   }

data SomeFunctionOverride p sym ext =
  forall args ret . SomeFunctionOverride (FunctionOverride p sym args ext ret)

buildCallocOverride :: ( LCB.IsSymInterface sym
                       , LCLM.HasLLVMAnn sym
                       , ?memOpts :: LCLM.MemOptions
                       , LCLM.HasPtrWidth w
                       )
                    => PN.NatRepr w
                    -> LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildCallocOverride ptrW mvar = FunctionOverride
  { functionName = "calloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ptrW Ctx.:> LCLM.LLVMPointerRepr ptrW
  , functionReturnType = LCLM.LLVMPointerRepr ptrW
  , functionOverride = \sym args -> Ctx.uncurryAssignment (callCalloc ptrW sym mvar) args
  }

callCalloc :: (LCB.IsSymInterface sym
              , LCLM.HasLLVMAnn sym
              , ?memOpts :: LCLM.MemOptions
              , LCLM.HasPtrWidth w
              )
           => PN.NatRepr w
           -> sym
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -- ^ The number of elements in the array
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callCalloc ptrW sym mvar (LCS.regValue -> num) (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let ?ptrWidth = ptrW
     numBV <- LCLM.projectLLVM_bv sym num
     szBV  <- LCLM.projectLLVM_bv sym sz
     LCLM.doCalloc sym mem szBV numBV LCLD.noAlignment

buildMallocOverride :: ( LCB.IsSymInterface sym
                       , ?memOpts :: LCLM.MemOptions
                       , LCLM.HasLLVMAnn sym
                       , LCLM.HasPtrWidth w
                       )
                    => PN.NatRepr w
                    -> LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildMallocOverride ptrW mvar = FunctionOverride
  { functionName = "malloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ptrW
  , functionReturnType = LCLM.LLVMPointerRepr ptrW
  , functionOverride = \sym args -> Ctx.uncurryAssignment (callMalloc ptrW sym mvar) args
  }

callMalloc :: ( LCB.IsSymInterface sym
              , ?memOpts :: LCLM.MemOptions
              , LCLM.HasLLVMAnn sym
              , LCLM.HasPtrWidth w
              )
           => PN.NatRepr w
           -> sym
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callMalloc ptrW sym mvar (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let ?ptrWidth = ptrW
     let displayString = "<malloc function override>"
     szBV <- LCLM.projectLLVM_bv sym sz
     LCLM.doMalloc sym LCLM.HeapAlloc LCLM.Mutable displayString mem szBV LCLD.noAlignment

-------------------------------------------------------------------------------
-- Hacky Overrides
-------------------------------------------------------------------------------

-- These are crude overrides that are primarily meant as a shortcut to getting
-- something to work. We should replace these with proper solutions later.
-- See #19 for one possible way to do this.

hackyBumpMalloc :: ( LCB.IsSymInterface sym
                   , LCLM.HasPtrWidth w
                   )
                => PN.NatRepr w
                -> sym
                -> LCS.GlobalVar (LCLM.LLVMPointerType w)
                -- ^ Global pointing to end of heap bump allocation
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -- ^ The number of bytes to allocate
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
hackyBumpMalloc ptrW sym endGlob (LCS.regValue -> sz) = do
  szBv <- liftIO $ LCLM.projectLLVM_bv sym sz
  LCS.modifyGlobal endGlob $ \endPtr -> liftIO $ do
    -- Bump up end pointer
    endPtr' <- LCLM.ptrSub sym ptrW endPtr szBv
    return (endPtr', endPtr')

buildHackyBumpMallocOverride
  :: ( LCB.IsSymInterface sym
     , LCLM.HasPtrWidth w
     )
  => PN.NatRepr w
  -> LCS.GlobalVar (LCLM.LLVMPointerType w)
  -- ^ Global pointing to end of heap bump allocation
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildHackyBumpMallocOverride ptrW endGlob = FunctionOverride
  { functionName = "malloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ptrW
  , functionReturnType = LCLM.LLVMPointerRepr ptrW
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyBumpMalloc ptrW sym endGlob) args
  }

hackyBumpCalloc :: ( LCB.IsSymInterface sym
                   , LCLM.HasLLVMAnn sym
                   , LCLM.HasPtrWidth w
                   )
                => PN.NatRepr w
                -> sym
                -> LCS.GlobalVar (LCLM.LLVMPointerType w)
                -- ^ Global pointing to end of heap bump allocation
                -> LCS.GlobalVar LCLM.Mem
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -- ^ The number of elements in the array
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -- ^ The number of bytes to allocate
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
hackyBumpCalloc ptrW sym endGlob memVar (LCS.regValue -> num) (LCS.regValue -> sz) = do
  let ?ptrWidth = ptrW
  LCS.modifyGlobal endGlob $ \endPtr -> do
    res <- LCS.modifyGlobal memVar $ \mem -> liftIO $ do
      -- Bump up end pointer
      numBV <- LCLM.projectLLVM_bv sym num
      szBV  <- LCLM.projectLLVM_bv sym sz
      allocSzBv <- WI.bvMul sym numBV szBV
      endPtr' <- LCLM.ptrSub sym ptrW endPtr allocSzBv

      -- Zero memory
      zero <- WI.bvLit sym WI.knownNat (BVS.zero WI.knownNat)
      mem' <- LCLM.doMemset sym ptrW mem endPtr' zero allocSzBv
      return (endPtr', mem')
    return (res, res)

buildHackyBumpCallocOverride
  :: ( LCB.IsSymInterface sym
     , LCLM.HasLLVMAnn sym
     , LCLM.HasPtrWidth w
     )
  => PN.NatRepr w
  -> LCS.GlobalVar (LCLM.LLVMPointerType w)
  -> LCS.GlobalVar LCLM.Mem
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                          Ctx.::> LCLM.LLVMPointerType w) ext
                            (LCLM.LLVMPointerType w)
buildHackyBumpCallocOverride ptrW endGlob memVar = FunctionOverride
  { functionName = "calloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ptrW Ctx.:> LCLM.LLVMPointerRepr ptrW
  , functionReturnType = LCLM.LLVMPointerRepr ptrW
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyBumpCalloc ptrW sym endGlob memVar) args
  }

-- | Mock @free@ by doing nothing.
hackyFreeOverride :: ( LCB.IsSymInterface sym
                     , LCLM.HasPtrWidth w
                     )
                  => PN.NatRepr w
                  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext
                                            LCT.UnitType
hackyFreeOverride ptrW = FunctionOverride
  { functionName = "free"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ptrW
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyCallFree ptrW sym) args
  }

hackyCallFree :: LCB.IsSymInterface sym
              => PN.NatRepr w
              -> sym
              -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym LCT.UnitType)
hackyCallFree _ptrW _sym _ptr = pure ()

-- | Mock @gd_error_ex@ by doing nothing.
hackyGdErrorExOverride :: ( LCB.IsSymInterface sym
                          , LCLM.HasPtrWidth w
                          )
                       => PN.NatRepr w
                       -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                               Ctx.::> LCLM.LLVMPointerType w
                                                               Ctx.::> LCLM.LLVMPointerType w) ext
                                                 LCT.UnitType
hackyGdErrorExOverride ptrW = FunctionOverride
  { functionName = "gd_error_ex"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ptrW
                                 Ctx.:> LCLM.LLVMPointerRepr ptrW
                                 Ctx.:> LCLM.LLVMPointerRepr ptrW
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyCallGdErrorEx ptrW sym) args
  }

hackyCallGdErrorEx :: LCB.IsSymInterface sym
                   => PN.NatRepr w
                   -> sym
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                   -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym LCT.UnitType)
hackyCallGdErrorEx _ptrW _sym _priority _format _va_args = pure ()

-- | Mock @printf@ by doing nothing and returing zero.
hackyPrintfOverride :: ( LCB.IsSymInterface sym
                       , LCLM.HasPtrWidth w
                       )
                    => PN.NatRepr w
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
hackyPrintfOverride ptrW = FunctionOverride
  { functionName = "printf"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ptrW
                                 Ctx.:> LCLM.LLVMPointerRepr ptrW
  , functionReturnType = LCLM.LLVMPointerRepr ptrW
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyCallPrintf ptrW sym) args
  }

hackyCallPrintf :: ( LCB.IsSymInterface sym
                   , LCLM.HasPtrWidth w
                   )
                => PN.NatRepr w
                -> sym
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
hackyCallPrintf ptrW sym _format _va_args = liftIO $ do
  let intRepr = LCT.knownNat @32
  zeroBV <- WI.bvLit sym intRepr $ BVS.zero intRepr
  bvToPtr sym zeroBV ptrW

-------------------------------------------------------------------------------
-- Function Call ABI Specification
-------------------------------------------------------------------------------

-- Now we actually need to perform the architecture-specific mapping. We can
-- use the type-level information in the override signatures to help us (and
-- especially the type repr inside of the FunctionCall type)
--
-- Note that this is data rather than a class because there can be different
-- ABIs for a given architecture (e.g., Windows and Linux)
data FunctionABI arch sym p =
  FunctionABI {
    -- Given a full register state, extract all of the arguments we need for
    -- the function call
    functionIntegerArgumentRegisters
      :: forall atps
       . LCT.CtxRepr atps
      -- Types of argument registers
      -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
      -- Argument register values
      -> Ctx.Assignment (LCS.RegEntry sym) atps
      -- Function argument values

    -- Build an OverrideSim action with appropriate return register types from
    -- a given OverrideSim action
  , functionIntegerReturnRegisters
     :: forall t r args rtp
      . LCT.TypeRepr t
     -- Function return type
     -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym t)
     -- OverrideSim action producing the functions's return value
     -> LCS.RegValue sym (DMS.ArchRegStruct arch)
     -- Argument register values from before function execution
     -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym (DMS.ArchRegStruct arch))
     -- OverrideSim action with return type matching system return register
     -- type

    -- A mapping from function names to overrides
  , functionNameMapping
     :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
     => Map.Map WF.FunctionName (SomeFunctionOverride p sym (DMS.MacawExt arch))
  }

-- A function to construct a FunctionABI with memory access
newtype BuildFunctionABI arch sym p = BuildFunctionABI (
       LCB.IsSymInterface sym
    => LCS.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
    -> LCS.GlobalVar LCLM.Mem
    -- MemVar for the execution
    -> [ SomeFunctionOverride p sym (DMS.MacawExt arch) ]
    -- Additional overrides
    -> FunctionABI arch sym p
  )

