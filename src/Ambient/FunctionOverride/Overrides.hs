{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Defines function overrides that are shared across different architectures.
module Ambient.FunctionOverride.Overrides
  ( -- * crucible-llvm–based overrides
    buildMallocOverride
  , callMalloc
  , buildCallocOverride
  , callCalloc
  , buildMemcpyOverride
  , callMemcpy
  , buildMemsetOverride
  , callMemset
    -- * Hacky overrides
  , buildHackyBumpMallocOverride
  , hackyBumpMalloc
  , buildHackyBumpCallocOverride
  , hackyBumpCalloc
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import           Ambient.FunctionOverride
import           Ambient.Override

-------------------------------------------------------------------------------
-- crucible-llvm–based overrides
-------------------------------------------------------------------------------

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

buildMemcpyOverride :: ( LCLM.HasPtrWidth w
                       , LCLM.HasLLVMAnn sym
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              LCT.UnitType
buildMemcpyOverride mvar = FunctionOverride
  { functionName = "memcpy"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callMemcpy bak mvar) args
  }

-- | Override for the @memcpy@ function. This behaves identically to the
-- corresponding override in @crucible-llvm@.
callMemcpy :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              , LCLM.HasLLVMAnn sym
              )
           => bak
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim p sym ext r args ret ()
callMemcpy bak mvar (LCS.regValue -> dest) (LCS.regValue -> src) (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do szBV <- LCLM.projectLLVM_bv bak sz
     let ?memOpts = overrideMemOptions
     mem' <- LCLM.doMemcpy bak (LCLM.ptrWidth sz) mem True dest src szBV
     pure ((), mem')

buildMemsetOverride :: ( LCLM.HasPtrWidth w
                       , LCLM.HasLLVMAnn sym
                       )
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w
                                                            Ctx.::> LCLM.LLVMPointerType w) ext
                                              LCT.UnitType
buildMemsetOverride mvar = FunctionOverride
  { functionName = "memset"
  , functionGlobals = []
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
                                 Ctx.:> LCLM.LLVMPointerRepr ?ptrWidth
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \bak args -> Ctx.uncurryAssignment (callMemset bak mvar) args
  }

-- | Override for the @memset@ function. This behaves identically to the
-- corresponding override in @crucible-llvm@.
callMemset :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              , LCLM.HasLLVMAnn sym
              )
           => bak
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
           -> LCS.OverrideSim p sym ext r args ret ()
callMemset bak mvar (LCS.regValue -> dest) val (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let w = LCLM.ptrWidth sz
     valBV <- ptrToBv8 bak w val
     szBV <- LCLM.projectLLVM_bv bak sz
     mem' <- LCLM.doMemset bak w mem dest (LCS.regValue valBV) szBV
     pure ((), mem')

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
