{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.FunctionOverride.X86_64.Linux (
    x86_64LinuxIntegerArguments
  , x86_64LinuxIntegerReturnRegisters
  , x86_64LinuxFunctionABI
  , x86_64LinuxTypes
  ) where

import           Control.Monad.IO.Class ( liftIO )
import           Data.Foldable ( foldl' )
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           GHC.TypeNats ( type (<=), KnownNat )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Data.Macaw.X86 as DMX
import qualified Data.Macaw.X86.X86Reg as DMXR
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Extensions as AE
import qualified Ambient.Override as AO
import qualified Ambient.Panic as AP
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.Extension as AFE
import qualified Ambient.FunctionOverride.Overrides as AFO
import qualified Ambient.FunctionOverride.StackArguments as AFS
import qualified Ambient.FunctionOverride.X86_64.Linux.Specialized as AFXLS

-- | Extract integer arguments from the corresponding six x86_64 registers.
-- Any additional arguments are read from the stack at @8(%rsp)@, @16(%rsp)@,
-- etc.
x86_64LinuxIntegerArguments
  :: forall atps sym bak mem
   . ( LCB.IsSymBackend sym bak
     , LCLM.HasLLVMAnn sym
     , ?memOpts :: LCLM.MemOptions
     )
  => bak
  -> DMS.GenArchVals mem DMX.X86_64
  -- ^ x86_64-specific architecture information
  -> LCT.CtxRepr atps
  -- ^ Types of argument registers
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes DMX.X86_64)
  -- ^ Argument register values
  -> LCLM.MemImpl sym
  -- ^ The memory state at the time of the function call
  -> IO (Ctx.Assignment (LCS.RegEntry sym) atps, AF.GetVarArg sym)
x86_64LinuxIntegerArguments bak archVals argTypes regs mem = do
  let ?ptrWidth = ptrWidth
  let stackArgList =
        map (AFS.loadIntegerStackArgument bak archVals regs mem)
             -- Note that we are starting the indices for stack arguments at 1,
             -- not 0, as the first stack argument is located at @8(%rsp)@
             -- instead of @0(%rsp)@ (which is where the return address
             -- resides).
             [1..]
  let argList = regArgList ++ stackArgList
  AO.buildArgumentAssignment bak argTypes argList
  where
    ptrWidth = WI.knownNat @64
    regArgList = map (pure . DMS.lookupReg archVals (LCS.RegEntry LCT.knownRepr regs)) DMX.x86ArgumentRegs

-- | Assemble x86_64 integer return register state from override return value.
x86_64LinuxIntegerReturnRegisters
  :: forall p sym bak ext r args rtp t mem
   . ( LCB.IsSymBackend sym bak )
  => bak
  -> DMS.GenArchVals mem DMX.X86_64
  -- ^ x86_64-specific architecture information
  -> LCT.TypeRepr t
  -- ^ Override return type
  -> LCS.OverrideSim p sym ext r args rtp (AF.OverrideResult sym DMX.X86_64 t)
  -- ^ OverrideSim action producing the override's return value
  -> LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64)
  -- ^ Argument register values from before override execution
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64))
x86_64LinuxIntegerReturnRegisters bak archVals ovTyp ovSim initRegs = do
  case ovTyp of
    LCT.UnitRepr -> do
      result <- ovSim
      pure $ updateRegs initRegs (AF.regUpdates result)
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @64) -> do
      result <- ovSim
      pure $ updateRegs initRegs ((DMXR.RAX, AF.result result) : AF.regUpdates result)
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @8) -> do
      (regs, result) <- bvZext ovSim
      pure $ updateRegs regs (AF.regUpdates result)
    LCLM.LLVMPointerRepr w
      | Just WI.Refl <- WI.testEquality w (WI.knownNat @32) -> do
      (regs, result) <- bvZext ovSim
      pure $ updateRegs regs (AF.regUpdates result)
    _ -> AP.panic AP.FunctionOverride
                  "x86_64LinuxIntegerReturnRegisters"
                  ["Unsupported override return type: " ++ show ovTyp]
    -- NOTE: If we encounter an override that returns a 128 bit int we'll
    -- need to add support for that here
  where
    sym = LCB.backendGetSym bak

    -- | Zero extend an LLMVPointer in region 0 (a bitvector) to fit in an
    -- integer register
    bvZext
      :: (1 <= srcW, KnownNat srcW)
      => LCS.OverrideSim p sym ext r args rtp (AF.OverrideResult sym DMX.X86_64 (LCLM.LLVMPointerType srcW))
      -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64), AF.OverrideResult sym DMX.X86_64 (LCLM.LLVMPointerType srcW))
    bvZext ov = do
      result <- ov
      asBv <- liftIO $ LCLM.projectLLVM_bv bak (AF.result result)
      asPtr <- liftIO $ AO.bvToPtr sym asBv (WI.knownNat @64)
      return (updateRegs initRegs [(DMXR.RAX, asPtr)], result)

    updateRegs :: LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64)
               -> [( DMC.ArchReg DMX.X86_64 (DMT.BVType 64)
                   , LCLM.LLVMPtr sym 64)]
               -> LCS.RegValue sym (DMS.ArchRegStruct DMX.X86_64)
    updateRegs regs regUpdates =
      foldl' (\r (reg, val) ->
               LCS.regValue $ DMS.updateReg archVals
                                            (LCS.RegEntry LCT.knownRepr r)
                                            reg
                                            val)
             regs
             regUpdates

x86_64LinuxFunctionABI :: ( LCLM.HasLLVMAnn sym
                          , ?memOpts :: LCLM.MemOptions )
                       => AF.BuildFunctionABI DMX.X86_64 sym (AE.AmbientSimulatorState sym DMX.X86_64)
x86_64LinuxFunctionABI = AF.BuildFunctionABI $ \fovCtx fs initialMem archVals unsupportedRelocs addrOvs namedOvs ->
  let ?ptrWidth = PN.knownNat @64 in
  -- NOTE: The order of elements in customNamedOvs is important.  See @Note
  -- [Override Specialization Order]@ for more information.
  let customNamedOvs = AFO.builtinGenericOverrides fovCtx fs initialMem unsupportedRelocs
                    ++ AFXLS.x86_64LinuxSpecializedOverrides
  in AF.FunctionABI { AF.functionIntegerArguments = \bak ->
                        x86_64LinuxIntegerArguments bak archVals
                    , AF.functionMainArgumentRegisters = (DMXR.RDI, DMXR.RSI)
                    , AF.functionIntegerReturnRegisters = x86_64LinuxIntegerReturnRegisters
                    , AF.functionNameMapping =
                      Map.fromListWith (<>)
                                       [ (AF.functionName fo, sfo NEL.:| [])
                                       | sfo@(AF.SomeFunctionOverride fo) <-
                                           customNamedOvs ++ namedOvs
                                       ]
                    , AF.functionAddrMapping = addrOvs
                    }

-- | A lookup function from 'AFE.TypeAlias' to types with the appropriate width
-- on X86_64 Linux.
x86_64LinuxTypes :: AFE.TypeLookup
x86_64LinuxTypes = AFE.TypeLookup $ \tp ->
  case tp of
    AFE.Byte -> Some (LCT.BVRepr (PN.knownNat @8))
    AFE.Int -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Long -> Some (LCT.BVRepr (PN.knownNat @64))
    AFE.PidT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Pointer -> Some (LCLM.LLVMPointerRepr (PN.knownNat @64))
    AFE.SizeT -> Some (LCT.BVRepr (PN.knownNat @64))
    AFE.UidT -> Some (LCT.BVRepr (PN.knownNat @32))

{-
Note [Override Specialization Order]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The order in which overrides appear in @customNamedOvs@ in
'x86_64LinuxFunctionABI' and the AArch32 equivalent function
'Ambient.FunctionOverride.AArch32.Linux.aarch32LinuxFunctionABI' determines the
hierarchy of overrides that specialize or refine other overrides.  In the event
that multiple overrides in this list have the same name, the verifier will
treat overrides later in the list as children of overrides earlier in the list.
Child overrides receive a list of their parents on invocation and may
optionally call into parent overrides.

We chose this design for the flexibility it provides.  It allows specialized
child overrides to insert computation before and/or after calling into parent
overrides.  It also allows child overrides to completely replace parent
overrides by simply not calling into the parent override.

For example, a child override may call into a parent override, then modify
register state to capture a side effect to a caller saved register (such as in
our specialized @sprintf@ override in
'Ambient.FunctionOverride.X86_64.Linux.Specialized').
-}
