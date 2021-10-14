{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
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
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx

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
                       :: sym
                       -> Ctx.Assignment (LCS.RegEntry sym) args
                       -- ^ Arguments to function
                       -> (forall rtp args' ret'. LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret))
                   -- ^ Override capturing behavior of the function
                   }

data SomeFunctionOverride p sym ext =
  forall args ret . SomeFunctionOverride (FunctionOverride p sym args ext ret)

buildCallocOverride :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                                            Ctx.::> LCLM.LLVMPointerType 64) ext
                                              (LCLM.LLVMPointerType 64)
buildCallocOverride mvar = FunctionOverride
  { functionName = "calloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCLM.LLVMPointerRepr LCT.knownNat
  , functionOverride = \sym args -> Ctx.uncurryAssignment (callCalloc sym mvar) args
  }

callCalloc :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
           => sym
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
              -- ^ The number of elements in the array
           -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
callCalloc sym mvar (LCS.regValue -> num) (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let ?ptrWidth = LCT.knownNat @64
     numBV <- LCLM.projectLLVM_bv sym num
     szBV  <- LCLM.projectLLVM_bv sym sz
     LCLM.doCalloc sym mem szBV numBV LCLD.noAlignment

buildMallocOverride :: LCB.IsSymInterface sym
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64) ext
                                              (LCLM.LLVMPointerType 64)
buildMallocOverride mvar = FunctionOverride
  { functionName = "malloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCLM.LLVMPointerRepr LCT.knownNat
  , functionOverride = \sym args -> Ctx.uncurryAssignment (callMalloc sym mvar) args
  }

callMalloc :: LCB.IsSymInterface sym
           => sym
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
callMalloc sym mvar (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let ?ptrWidth = LCT.knownNat @64
     let displayString = "<malloc function override>"
     szBV <- LCLM.projectLLVM_bv sym sz
     LCLM.doMalloc sym LCLM.HeapAlloc LCLM.Mutable displayString mem szBV LCLD.noAlignment

-------------------------------------------------------------------------------
-- Hacky Overrides
-------------------------------------------------------------------------------

-- These are crude overrides that are primarily meant as a shortcut to getting
-- something to work. We should replace these with proper solutions later.
-- See #19 for one possible way to do this.

-- | Mock @free@ by doing nothing.
hackyFreeOverride :: LCB.IsSymInterface sym
                  => FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64) ext
                                            LCT.UnitType
hackyFreeOverride = FunctionOverride
  { functionName = "free"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyCallFree sym) args
  }

hackyCallFree :: LCB.IsSymInterface sym
              => sym
              -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
              -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym LCT.UnitType)
hackyCallFree _sym _ptr = pure ()

-- | Mock @gd_error_ex@ by doing nothing.
hackyGdErrorExOverride :: LCB.IsSymInterface sym
                       => FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                                               Ctx.::> LCLM.LLVMPointerType 64
                                                               Ctx.::> LCLM.LLVMPointerType 64) ext
                                                 LCT.UnitType
hackyGdErrorExOverride = FunctionOverride
  { functionName = "gd_error_ex"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                                 Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                                 Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyCallGdErrorEx sym) args
  }

hackyCallGdErrorEx :: LCB.IsSymInterface sym
                   => sym
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                   -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym LCT.UnitType)
hackyCallGdErrorEx _sym _priority _format _va_args = pure ()

-- | Mock @printf@ by doing nothing and returing zero.
hackyPrintfOverride :: LCB.IsSymInterface sym
                    => FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                                            Ctx.::> LCLM.LLVMPointerType 64) ext
                                              (LCLM.LLVMPointerType 64)
hackyPrintfOverride = FunctionOverride
  { functionName = "printf"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                                 Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCLM.LLVMPointerRepr LCT.knownNat
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyCallPrintf sym) args
  }

hackyCallPrintf :: LCB.IsSymInterface sym
                => sym
                -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
hackyCallPrintf sym _format _va_args = liftIO $ do
  let intRepr = LCT.knownNat @32
  zeroBV <- WI.bvLit sym intRepr $ BVS.zero intRepr
  bvToPtr sym zeroBV

-------------------------------------------------------------------------------
-- Function Call ABI Specification
-------------------------------------------------------------------------------

-- Now we actually need to perform the architecture-specific mapping. We can
-- use the type-level information in the override signatures to help us (and
-- especially the type repr inside of the FunctionCall type)
--
-- Note that this is data rather than a class because there can be different
-- ABIs for a given architecture (e.g., Windows and Linux)
data FunctionABI arch =
  FunctionABI {
    -- Given a full register state, extract all of the arguments we need for
    -- the function call
    functionIntegerArgumentRegisters
      :: forall sym atps
       . LCT.CtxRepr atps
      -- ^ Types of argument registers
      -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
      -- ^ Argument register values
      -> Ctx.Assignment (LCS.RegEntry sym) atps
      -- ^ Function argument values

    -- Build an OverrideSim action with appropriate return register types from
    -- a given OverrideSim action
  , functionIntegerReturnRegisters
     :: forall t p sym ext r args rtp
      . LCT.TypeRepr t
     -- ^ Function return type
     -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym t)
     -- ^ OverrideSim action producing the functions's return value
     -> LCS.RegValue sym (DMS.ArchRegStruct arch)
     -- ^ Argument register values from before function execution
     -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct arch))
     -- ^ OverrideSim action with return type matching system return register
     -- type

    -- A mapping from function names to overrides
  , functionNameMapping
     :: forall p sym ext
      . (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
     => Map.Map WF.FunctionName (SomeFunctionOverride p sym ext)
  }

-- A function to construct a FunctionABI with memory access
newtype BuildFunctionABI arch = BuildFunctionABI (
    LCS.GlobalVar LCLM.Mem
    -- ^ MemVar for the execution
    -> FunctionABI arch
  )
