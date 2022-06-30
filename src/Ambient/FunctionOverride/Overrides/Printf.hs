{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Defines overrides and helper functions to support the printf family of
-- functions

module Ambient.FunctionOverride.Overrides.Printf
  ( buildSprintfOverride
  , callSprintf
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.State as CMS
import qualified Data.BitVector.Sized as BVS
import qualified Data.Char as C
import           Data.Foldable.WithIndex ( ifoldlM )
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Vector as DV
import qualified GHC.Stack as GHC

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.Printf as LCLP
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified What4.InterpretedFloatingPoint as WIFloat
import qualified What4.Protocol.Online as WPO
import qualified What4.Symbol as WS

import qualified Ambient.Extensions as AExt
import           Ambient.FunctionOverride
import qualified Ambient.Memory as AM
import           Ambient.Override

-- | Override for the @sprintf@ function.  This override has the limitation
-- that all string arguments must be concrete.  This override adds failing
-- assertions for symbolic strings.  The override renders symbolic integers as
-- @?@ characters.  See ticket #118.
callSprintf
  :: forall sym bak w p ext r args ret arch scope st fs solver
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , DMC.MemWidth w
     , p ~ AExt.AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     , ?memOpts :: LCLM.MemOptions
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ LCBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     )
  => bak
  -> AM.InitialMemory sym w
  -- ^ Initial memory state for symbolic execution
  -> Map.Map (DMC.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> Ctx.Assignment (LCS.RegEntry sym)
                    (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                  Ctx.::> LCLM.LLVMPointerType w)
  -- ^ The non-variadic arguments, consisting of (1) the output pointer, and
  -- (2) the format string
  -> GetVarArg sym
  -- ^ The variadic arguments
  -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callSprintf bak initialMem unsupportedRelocs
  (Ctx.Empty Ctx.:> (LCS.regValue -> outPtr) Ctx.:> strPtr) gva = do
    let mvar = AM.imMemVar initialMem
    mem0 <- LCS.readGlobal mvar
    -- Read format string
    formatStr <- AExt.loadString bak mem0 initialMem unsupportedRelocs strPtr Nothing
    -- Parse format directives
    case LCLP.parseDirectives formatStr of
      Left err -> LCS.overrideError $
        LCS.AssertFailureSimError "Format string parsing failed" err
      Right ds -> do
        -- Compute output
        valist <- liftIO $ getPrintfVarArgs (DV.fromList ds) gva
        ((str, n), mem1) <-
          CMS.runStateT
            (LCLP.executeDirectives (printfOps bak initialMem unsupportedRelocs valist)
                                    ds)
            mem0

        -- Convert resulting string into an array
        let arrayName = WS.safeSymbol "sprintf output"
        let arrayRepr =
              WI.BaseArrayRepr (Ctx.singleton (WI.BaseBVRepr ?ptrWidth))
                               (WI.BaseBVRepr (WI.knownNat @8))
        symArray <- liftIO $ WI.freshConstant sym arrayName arrayRepr
        symArray' <- liftIO $ populateArray symArray str

        -- Write to output pointer
        nBv <- liftIO $ WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth (toInteger n))
        mem2 <- liftIO $ LCLM.doArrayStore bak mem1 outPtr LCLD.noAlignment symArray' nBv
        LCS.writeGlobal mvar mem2
        liftIO $ bvToPtr sym nBv ?ptrWidth
  where
    sym = LCB.backendGetSym bak

    populateArray
      :: WI.SymArray sym (LCT.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8)
      -> String
      -> IO (WI.SymArray sym (LCT.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8))
    populateArray array str = ifoldlM updateArray array str

    updateArray
      :: Int
      -> WI.SymArray sym (LCT.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8)
      -> Char
      -> IO (WI.SymArray sym (LCT.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8))
    updateArray index array char = do
      index_bv <- liftIO $ WI.bvLit sym ?ptrWidth (BVS.mkBV ?ptrWidth (fromIntegral index))
      char_bv <- liftIO $ WI.bvLit sym (WI.knownNat @8) (BVS.mkBV (WI.knownNat @8) (fromIntegral (C.ord char)))
      WI.arrayUpdate sym array (Ctx.singleton index_bv) char_bv

buildSprintfOverride
  :: ( DMC.MemWidth w
     , LCLM.HasPtrWidth w
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     , p ~ AExt.AmbientSimulatorState sym arch
     , w ~ DMC.ArchAddrWidth arch
     )

  => AM.InitialMemory sym w
  -- ^ Initial memory state for symbolic execution
  -> Map.Map (DMC.MemWord w) String
  -- ^ Mapping from unsupported relocation addresses to the names of the
  -- unsupported relocation types.
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                          Ctx.::> LCLM.LLVMPointerType w) ext
                            (LCLM.LLVMPointerType w)
buildSprintfOverride initialMem unsupportedRelocs =
  WI.withKnownNat ?ptrWidth $
  mkVariadicFunctionOverride "sprintf" $ \bak args getVarArg ->
    callSprintf bak initialMem unsupportedRelocs args getVarArg

-- | Define handlers for the various printf directives.
--
-- NOTE: The only difference between this function and the version defined in
-- Crucible is that this function uses the Ambient-specific @loadString@
-- function.
printfOps :: ( LCB.IsSymBackend sym bak
             , LCLM.HasLLVMAnn sym
             , LCLM.HasPtrWidth w
             , DMC.MemWidth w
             , WPO.OnlineSolver solver
             , ?memOpts :: LCLM.MemOptions
             , sym ~ WE.ExprBuilder scope st fs
             , bak ~ LCBO.OnlineBackend solver scope st fs
             , p ~ AExt.AmbientSimulatorState sym arch
             , w ~ DMC.ArchAddrWidth arch
             )
          => bak
          -> AM.InitialMemory sym w
          -- ^ Initial memory state for symbolic execution
          -> Map.Map (DMC.MemWord w) String
          -- ^ Mapping from unsupported relocation addresses to the names of the
          -- unsupported relocation types.
          -> DV.Vector (LCS.AnyValue sym)
          -> LCLP.PrintfOperations (CMS.StateT (LCLM.MemImpl sym) (LCS.OverrideSim p sym ext r args ret))
printfOps bak initialMem unsupportedRelocs valist =
  let sym = LCB.backendGetSym bak in
  LCLP.PrintfOperations
  { LCLP.printfUnsupported = \x ->CMS.lift $ liftIO
                                           $ LCB.addFailedAssertion bak
                                           $ LCS.Unsupported GHC.callStack x

  , LCLP.printfGetInteger = \i sgn _len ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue (LCLM.LLVMPointerRepr w) x) ->
         do bv <- liftIO (LCLM.projectLLVM_bv bak x)
            if sgn then
              return $ BVS.asSigned w <$> WI.asBV bv
            else
              return $ BVS.asUnsigned <$> WI.asBV bv
       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf"
                    (unwords ["Expected integer, but got:", show tpr])
       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                   "Out-of-bounds argument access in printf"
                   (unwords ["Index:", show i])

  , LCLP.printfGetFloat = \i _len ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue (LCT.FloatRepr (_fi :: LCT.FloatInfoRepr fi)) x) ->
         do xr <- liftIO (WIFloat.iFloatToReal @_ @fi sym x)
            return (WI.asRational xr)
       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf."
                    (unwords ["Expected floating-point, but got:", show tpr])
       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Out-of-bounds argument access in printf:"
                    (unwords ["Index:", show i])

  , LCLP.printfGetString  = \i numchars ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue LCLM.PtrRepr ptr) ->
           do mem <- CMS.get
              let reg = LCS.RegEntry (LCLM.LLVMPointerRepr ?ptrWidth) ptr
              CMS.lift $ AExt.loadString bak mem initialMem unsupportedRelocs reg numchars
       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf."
                    (unwords ["Expected char*, but got:", show tpr])
       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Out-of-bounds argument access in printf:"
                    (unwords ["Index:", show i])

  , LCLP.printfGetPointer = \i ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue LCLM.PtrRepr ptr) ->
         return $ show (LCLM.ppPtr ptr)
       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf."
                    (unwords ["Expected void*, but got:", show tpr])
       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Out-of-bounds argument access in printf:"
                    (unwords ["Index:", show i])

  , LCLP.printfSetInteger = \i len v ->
     case valist DV.!? (i-1) of
       Just (LCS.AnyValue LCLM.PtrRepr ptr) ->
         do mem <- CMS.get
            case len of
              LCLP.Len_Byte  -> do
                 let w8 = WI.knownNat :: WI.NatRepr 8
                 let tp = LCLM.bitvectorType 1
                 x <- liftIO (LCLM.llvmPointer_bv sym =<< WI.bvLit sym w8 (BVS.mkBV w8 (toInteger v)))
                 mem' <- liftIO $ LCLM.doStore bak mem ptr (LCLM.LLVMPointerRepr w8) tp LCLD.noAlignment x
                 CMS.put mem'
              LCLP.Len_Short -> do
                 let w16 = WI.knownNat :: WI.NatRepr 16
                 let tp = LCLM.bitvectorType 2
                 x <- liftIO (LCLM.llvmPointer_bv sym =<< WI.bvLit sym w16 (BVS.mkBV w16 (toInteger v)))
                 mem' <- liftIO $ LCLM.doStore bak mem ptr (LCLM.LLVMPointerRepr w16) tp LCLD.noAlignment x
                 CMS.put mem'
              LCLP.Len_NoMod -> do
                 let w32  = WI.knownNat :: WI.NatRepr 32
                 let tp = LCLM.bitvectorType 4
                 x <- liftIO (LCLM.llvmPointer_bv sym =<< WI.bvLit sym w32 (BVS.mkBV w32 (toInteger v)))
                 mem' <- liftIO $ LCLM.doStore bak mem ptr (LCLM.LLVMPointerRepr w32) tp LCLD.noAlignment x
                 CMS.put mem'
              LCLP.Len_Long  -> do
                 let w64 = WI.knownNat :: WI.NatRepr 64
                 let tp = LCLM.bitvectorType 8
                 x <- liftIO (LCLM.llvmPointer_bv sym =<< WI.bvLit sym w64 (BVS.mkBV w64 (toInteger v)))
                 mem' <- liftIO $ LCLM.doStore bak mem ptr (LCLM.LLVMPointerRepr w64) tp LCLD.noAlignment x
                 CMS.put mem'
              _ ->
                CMS.lift $ liftIO
                         $ LCB.addFailedAssertion bak
                         $ LCS.Unsupported GHC.callStack
                         $ unwords ["Unsupported size modifier in %n conversion:", show len]

       Just (LCS.AnyValue tpr _) ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Type mismatch in printf."
                    (unwords ["Expected void*, but got:", show tpr])

       Nothing ->
         CMS.lift $ liftIO
                  $ LCB.addFailedAssertion bak
                  $ LCS.AssertFailureSimError
                    "Out-of-bounds argument access in printf:"
                    (unwords ["Index:", show i])
  }

-- | Given the directives in a @printf@-style format string, retrieve the
-- corresponding variadic arguments. See @Note [Varargs]@ in
-- "Ambient.FunctionOverride" for a more detailed explanation of the mechanisms
-- at play.
getPrintfVarArgs ::
  forall sym w.
  LCLM.HasPtrWidth w =>
  DV.Vector LCLP.PrintfDirective ->
  GetVarArg sym ->
  IO (DV.Vector (LCS.AnyValue sym))
getPrintfVarArgs pds =
  CMS.evalStateT (DV.mapMaybeM (CMS.StateT . getPrintfVarArg) pds)

-- | Given a single directive in a @printf@-style format string:
--
-- * If it is a conversion directive (i.e., beginning with a @%@ character),
--   retrieve a variadic argument @arg@ of the corresponding type and return
--   @'Just' (arg, gva)@, where @gva@ is the callback for retrieving the next
--   variadic argument. See @Note [Varargs]@ in "Ambient.FunctionOverride".
--
-- * Otherwise, return 'Nothing'.
getPrintfVarArg ::
  forall sym w.
  LCLM.HasPtrWidth w =>
  LCLP.PrintfDirective ->
  GetVarArg sym ->
  IO (Maybe (LCS.AnyValue sym), GetVarArg sym)
getPrintfVarArg pd gva@(GetVarArg getVarArg) =
  case pd of
    LCLP.StringDirective{} -> pure (Nothing, gva)
    LCLP.ConversionDirective cd ->
      case LCLP.printfType cd of
        LCLP.Conversion_Integer{}    -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_Char{}       -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_String{}     -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_Pointer{}    -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_CountChars{} -> getArgWithType LCLM.PtrRepr
        LCLP.Conversion_Floating{}   -> getArgWithType $ LCT.FloatRepr WIFloat.DoubleFloatRepr
  where
    getArgWithType ::
      forall arg.
      LCT.TypeRepr arg ->
      IO (Maybe (LCS.AnyValue sym), GetVarArg sym)
    getArgWithType tpRepr = do
      (LCS.RegEntry ty val, gva') <- getVarArg tpRepr
      pure (Just (LCS.AnyValue ty val), gva')
