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
  , FunctionOverrideHandle
  , FunctionABI(..)
  , BuildFunctionABI(..)
    -- * Overrides
  , buildMallocOverride
  , buildCallocOverride
    -- * Hacky overrides
  , buildHackyBumpMallocOverride
  , buildHackyBumpCallocOverride
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI

-------------------------------------------------------------------------------
-- Function Call Overrides
-------------------------------------------------------------------------------

-- | FunctionOverride captures an override and type information about how to
-- call it
data FunctionOverride p sym args ext ret =
  FunctionOverride { functionName :: WF.FunctionName
                   -- ^ Name of the function
                   , functionGlobals :: [Some LCS.GlobalVar]
                   -- ^ Global variables the function uses
                   , functionArgTypes :: LCT.CtxRepr args
                   -- ^ Types of the arguments to the function
                   , functionReturnType :: LCT.TypeRepr ret
                   -- ^ Return type of the function
                   , functionOverride
                       :: forall bak
                        . (LCB.IsSymBackend sym bak)
                       => bak
                       -> Ctx.Assignment (LCS.RegEntry sym) args
                       -- Arguments to function
                       -> (forall rtp args' ret'. LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret))
                   -- ^ Override capturing behavior of the function
                   }

data SomeFunctionOverride p sym ext =
  forall args ret . SomeFunctionOverride (FunctionOverride p sym args ext ret)

-- | A 'LCF.FnHandle' for a function override.
type FunctionOverrideHandle arch =
  LCF.FnHandle
    (LCT.EmptyCtx LCT.::> LCT.StructType (DMS.MacawCrucibleRegTypes arch))
    (LCT.StructType (DMS.MacawCrucibleRegTypes arch))

buildCallocOverride :: ( LCLM.HasLLVMAnn sym
                       , ?memOpts :: LCLM.MemOptions
                       , LCLM.HasPtrWidth w
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildCallocOverride mvar = FunctionOverride
  { functionName = "calloc"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callCalloc bak mvar) args
  }

callCalloc :: ( LCB.IsSymBackend sym bak
              , LCLM.HasLLVMAnn sym
              , ?memOpts :: LCLM.MemOptions
              , LCLM.HasPtrWidth w
              )
           => bak
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -- ^ The number of elements in the array
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callCalloc bak mvar (LCS.regValue -> num) (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do numBV <- LCLM.projectLLVM_bv bak num
     szBV  <- LCLM.projectLLVM_bv bak sz
     LCLM.doCalloc bak mem szBV numBV LCLD.noAlignment

buildMallocOverride :: ( ?memOpts :: LCLM.MemOptions
                       , LCLM.HasLLVMAnn sym
                       , LCLM.HasPtrWidth w
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildMallocOverride mvar = FunctionOverride
  { functionName = "malloc"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callMalloc bak mvar) args
  }

callMalloc :: ( LCB.IsSymBackend sym bak
              , ?memOpts :: LCLM.MemOptions
              , LCLM.HasLLVMAnn sym
              , LCLM.HasPtrWidth w
              )
           => bak
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callMalloc bak mvar (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let displayString = "<malloc function override>"
     szBV <- LCLM.projectLLVM_bv bak sz
     LCLM.doMalloc bak LCLM.HeapAlloc LCLM.Mutable displayString mem szBV LCLD.noAlignment

-------------------------------------------------------------------------------
-- Hacky Overrides
-------------------------------------------------------------------------------

-- These are crude overrides that are primarily meant as a shortcut to getting
-- something to work. We should replace these with proper solutions later.
-- See #19 for one possible way to do this.

hackyBumpMalloc :: ( LCB.IsSymBackend sym bak
                   , LCLM.HasPtrWidth w
                   )
                => bak
                -> LCS.GlobalVar (LCLM.LLVMPointerType w)
                -- ^ Global pointing to end of heap bump allocation
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -- ^ The number of bytes to allocate
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
hackyBumpMalloc bak endGlob (LCS.regValue -> sz) = do
  let sym = LCB.backendGetSym bak
  szBv <- liftIO $ LCLM.projectLLVM_bv bak sz
  LCS.modifyGlobal endGlob $ \endPtr -> liftIO $ do
    -- Bump up end pointer
    endPtr' <- LCLM.ptrSub sym ?ptrWidth endPtr szBv
    return (endPtr', endPtr')

buildHackyBumpMallocOverride
  :: LCLM.HasPtrWidth w
  => LCS.GlobalVar (LCLM.LLVMPointerType w)
  -- ^ Global pointing to end of heap bump allocation
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext
                                              (LCLM.LLVMPointerType w)
buildHackyBumpMallocOverride endGlob = FunctionOverride
  { functionName = "malloc"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (hackyBumpMalloc bak endGlob) args
  }

hackyBumpCalloc :: ( LCB.IsSymBackend sym bak
                   , LCLM.HasLLVMAnn sym
                   , LCLM.HasPtrWidth w
                   )
                => bak
                -> LCS.GlobalVar (LCLM.LLVMPointerType w)
                -- ^ Global pointing to end of heap bump allocation
                -> LCS.GlobalVar LCLM.Mem
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -- ^ The number of elements in the array
                -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
                -- ^ The number of bytes to allocate
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
hackyBumpCalloc bak endGlob memVar (LCS.regValue -> num) (LCS.regValue -> sz) = do
  let sym = LCB.backendGetSym bak
  LCS.modifyGlobal endGlob $ \endPtr -> do
    res <- LCS.modifyGlobal memVar $ \mem -> liftIO $ do
      -- Bump up end pointer
      numBV <- LCLM.projectLLVM_bv bak num
      szBV  <- LCLM.projectLLVM_bv bak sz
      allocSzBv <- WI.bvMul sym numBV szBV
      endPtr' <- LCLM.ptrSub sym ?ptrWidth endPtr allocSzBv

      -- Zero memory
      zero <- WI.bvLit sym WI.knownNat (BVS.zero WI.knownNat)
      mem' <- LCLM.doMemset bak ?ptrWidth mem endPtr' zero allocSzBv
      return (endPtr', mem')
    return (res, res)

buildHackyBumpCallocOverride
  :: ( LCLM.HasLLVMAnn sym
     , LCLM.HasPtrWidth w
     )
  => LCS.GlobalVar (LCLM.LLVMPointerType w)
  -> LCS.GlobalVar LCLM.Mem
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                          Ctx.::> LCLM.LLVMPointerType w) ext
                            (LCLM.LLVMPointerType w)
buildHackyBumpCallocOverride endGlob memVar = FunctionOverride
  { functionName = "calloc"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , functionOverride = \bak args -> Ctx.uncurryAssignment (hackyBumpCalloc bak endGlob memVar) args
  }

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
      :: forall bak atps
       . LCB.IsSymBackend sym bak
      => bak
      -> LCT.CtxRepr atps
      -- Types of argument registers
      -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
      -- Argument register values
      -> IO (Ctx.Assignment (LCS.RegEntry sym) atps)
      -- Function argument values

    -- Build an OverrideSim action with appropriate return register types from
    -- a given OverrideSim action
  , functionIntegerReturnRegisters
     :: forall bak t r args rtp
      . LCB.IsSymBackend sym bak
     => bak
     -> LCT.TypeRepr t
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

    -- A mapping of function addresses to addresses, which represents
    -- kernel-provided user helpers that are reachable from user space at fixed
    -- addresses in kernel memory.
    --
    -- One alternative to this design would be to augment the Macaw-loaded
    -- Memory with the right addresses, but this proves tricky to set up. As a
    -- result, we simply specify the kernel-provided helpers on the side.
  , functionKernelAddrMapping
     :: Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch))
                (SomeFunctionOverride p sym (DMS.MacawExt arch))
  }

-- A function to construct a FunctionABI with memory access
newtype BuildFunctionABI arch sym p = BuildFunctionABI (
       LCS.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
    -> LCS.GlobalVar LCLM.Mem
    -- MemVar for the execution
    -> [ SomeFunctionOverride p sym (DMS.MacawExt arch) ]
    -- Additional overrides
    -> Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch))
               (SomeFunctionOverride p sym (DMS.MacawExt arch))
    -- Overrides for kernel-provided user helpers
    -> FunctionABI arch sym p
  )

