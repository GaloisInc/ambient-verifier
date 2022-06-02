{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module provides definitions to support the 32 bit Linux ABI for AArch32
--
-- See <https://github.com/ARM-software/abi-aa/releases> for details
module Ambient.FunctionOverride.AArch32.Linux (
    aarch32LinuxFunctionABI
  , aarch32LinuxTypes
  ) where

import           Control.Lens ( use )
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.Map as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )

import qualified Data.Macaw.AArch32.Symbolic as DMAS
import qualified Data.Macaw.ARM as DMA
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import qualified Data.Macaw.Symbolic as DMS
import qualified Language.ASL.Globals as ASL
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Common as LCCC
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.ExecutionTree as LCSE
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Types as LCT

import qualified Ambient.Extensions as AE
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.Extension as AFE
import qualified Ambient.FunctionOverride.Overrides as AFO
import qualified Ambient.Memory as AM
import qualified Ambient.Override as AO
import qualified Ambient.Panic as AP

-- | Integer arguments are passed in the first four registers in ARM
aarch32LinuxIntegerArgumentRegisters
  :: forall atps sym bak
   . (LCB.IsSymBackend sym bak)
  => bak
  -> LCT.CtxRepr atps
  -- ^ The argument types
  -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes DMA.ARM)
  -- ^ A register structure containing symbolic values
  -> IO (Ctx.Assignment (LCS.RegEntry sym) atps)
aarch32LinuxIntegerArgumentRegisters bak argTypes regFile =
  AO.buildArgumentRegisterAssignment bak argTypes regList
  where
    ptrWidth = PN.knownNat @32
    regList = map lookupReg [ ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
                            , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")
                            , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2")
                            , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3")
                            ]
    lookupReg r = LCS.RegEntry (LCLM.LLVMPointerRepr ptrWidth)
                               (LCS.unRV (DMAS.lookupReg r regFile))

-- | Inject override return values back into the register state
--
-- Void returns ('LCT.UnitRepr') have no effect.
--
-- Otherwise, an integer return value is placed into r0
aarch32LinuxIntegerReturnRegisters
  :: (LCB.IsSymBackend sym bak)
  => bak
  -> LCT.TypeRepr tp
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym tp)
  -> LCS.RegValue sym (DMS.ArchRegStruct DMA.ARM)
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (DMS.ArchRegStruct DMA.ARM))
aarch32LinuxIntegerReturnRegisters bak ovTy ovSim initRegs =
  case ovTy of
    LCT.UnitRepr -> ovSim >> return initRegs
    LCLM.LLVMPointerRepr w
      | Just PC.Refl <- PC.testEquality w (PN.knownNat @32) -> do
          result <- ovSim
          let r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
          return $! DMAS.updateReg r0 (const (LCS.RV result)) initRegs
    LCLM.LLVMPointerRepr w
      | Just PC.Refl <- PC.testEquality w (PN.knownNat @8) -> do
          -- Zero extend 8-bit return value to fit in 32-bit register
          result <- ovSim
          asBv <- liftIO $ LCLM.projectLLVM_bv bak result
          asPtr <- liftIO $ AO.bvToPtr sym asBv (PN.knownNat @32)
          let r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
          return $! DMAS.updateReg r0 (const (LCS.RV asPtr)) initRegs
    _ -> AP.panic AP.FunctionOverride "aarch32LinuxIntegerReturnRegisters" [ "Unsupported return type: " ++ show ovTy ]
  where
    sym = LCB.backendGetSym bak

-- | Model @__kuser_get_tls@ by returning the value stored in the TLS global
-- variable. See @Note [AArch32 and TLS]@.
buildKUserGetTLSOverride ::
     LCLM.HasPtrWidth w
  => LCCC.GlobalVar (LCLM.LLVMPointerType w)
     -- ^ Global variable for TLS
  -> AF.FunctionOverride p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType w)
buildKUserGetTLSOverride tlsGlob =
  PN.withKnownNat ?ptrWidth $
  AF.mkFunctionOverride "__kuser_get_tls" $ \bak args ->
    Ctx.uncurryAssignment (callKUserGetTLSOverride bak tlsGlob) args

callKUserGetTLSOverride ::
     ( LCB.IsSymBackend sym bak
     , LCLM.HasPtrWidth w
     )
  => bak
  -> LCCC.GlobalVar (LCLM.LLVMPointerType w)
     -- ^ Global variable for TLS
  -> LCS.OverrideSim p sym ext r args rtp (LCS.RegValue sym (LCLM.LLVMPointerType w))
callKUserGetTLSOverride _bak tlsGlob = do
  globState <- use (LCSE.stateTree . LCSE.actFrame . LCSE.gpGlobals)
  case LCSG.lookupGlobal tlsGlob globState of
    Nothing -> AP.panic AP.FunctionOverride "callKUserGetTLSOverride"
                 [ "Failed to find global TLS variable: "
                   ++ show (LCCC.globalName tlsGlob) ]
    Just tlsPtr -> pure tlsPtr

aarch32LinuxFunctionABI ::
     (?memOpts :: LCLM.MemOptions)
  => LCCC.GlobalVar (LCLM.LLVMPointerType 32)
     -- ^ Global variable for TLS
  -> AF.BuildFunctionABI DMA.ARM sym (AE.AmbientSimulatorState sym DMA.ARM)
aarch32LinuxFunctionABI tlsGlob = AF.BuildFunctionABI $ \fs initialMem unsupportedRelocs addrOvs namedOvs ->
  let ?recordLLVMAnnotation = \_ _ _ -> return () in
  let ?ptrWidth = PN.knownNat @32 in
  let memVar = AM.imMemVar initialMem in
  let memOverrides = [ AF.SomeFunctionOverride (AFO.buildMemcpyOverride initialMem)
                     , AF.SomeFunctionOverride (AFO.buildMemsetOverride initialMem)
                     , AF.SomeFunctionOverride (AFO.buildShmgetOverride memVar)
                     , AF.SomeFunctionOverride AFO.shmatOverride
                     , AF.SomeFunctionOverride (AFO.buildSprintfOverride initialMem unsupportedRelocs)
                     ] in
  let networkOverrides = AFO.networkOverrides fs initialMem unsupportedRelocs in
  let customKernelOvs =
        -- The addresses are taken from
        -- https://github.com/torvalds/linux/blob/5bfc75d92efd494db37f5c4c173d3639d4772966/Documentation/arm/kernel_user_helpers.rst
        [ -- __kuser_get_tls (See Note [AArch32 and TLS])
          (AF.AddrFromKernel 0xffff0fe0, AF.SomeFunctionOverride (buildKUserGetTLSOverride tlsGlob))
        ] in
  AF.FunctionABI { AF.functionIntegerArgumentRegisters = aarch32LinuxIntegerArgumentRegisters
                 , AF.functionMainArgumentRegisters =
                     ( ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
                     , ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")
                     )
                 , AF.functionIntegerReturnRegisters = aarch32LinuxIntegerReturnRegisters
                 , AF.functionNameMapping =
                     Map.fromList [ (AF.functionName fo, sfo)
                                  | sfo@(AF.SomeFunctionOverride fo) <-
                                      memOverrides ++ networkOverrides ++ namedOvs
                                  ]
                 , AF.functionAddrMapping =
                     Map.union (Map.fromList customKernelOvs) addrOvs
                 }

-- | A lookup function from 'AFE.TypeAlias' to types with the appropriate width
-- on Arm32 Linux.
aarch32LinuxTypes :: AFE.TypeLookup
aarch32LinuxTypes = AFE.TypeLookup $ \tp ->
  case tp of
    AFE.Byte -> Some (LCT.BVRepr (PN.knownNat @8))
    AFE.Int -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Long -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.PidT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.Pointer -> Some (LCLM.LLVMPointerRepr (PN.knownNat @32))
    AFE.SizeT -> Some (LCT.BVRepr (PN.knownNat @32))
    AFE.UidT -> Some (LCT.BVRepr (PN.knownNat @32))

{-
Note [AArch32 and TLS]
~~~~~~~~~~~~~~~~~~~~~~
AArch32 handles thread-local state (TLS) in the following ways:

1. The __ARM_NR_set_tls syscall sets the TLS value.
2. The __kuser_get_tls function returns the TLS value. (__kuser_get_tls is a
   special function provided by the Linux kernel—more on this in a bit.)

We do not currently model (1). The _start() function in a glibc-compiled binary
often performs (1), but we do not yet support glibc's implementation of
_start(). See #22.

On the other hand, (2) occurs whenever one invokes the syscall() function in
glibc, as their implementation of syscall() uses TLS for error-handling
purposes. To support this, we do the following:

* When initializing memory in AArch32, we create a global variable representing
  the TLS state and initialize it with a fresh symbolic value. See
  Ambient.Memory.AArch32.Linux.initTLSMemory. This is essentially the same
  approach that is used on the x86_64 side to handle fsbase and gsbase.
  (See Note [x86_64 and TLS] in A.Memory.X86_64.Linux.)

* The Linux kernel provides __kuser_get_tls at a fixed address in the user
  space of all running AArch32 binaries (see aarch32LinuxFunctionABI for the
  specific address). Macaw-loaded binaries do not display this address, but it
  is there nonetheless. To model these special addresses, a FunctionABI has a
  functionKernelAddrMapping that maps fixed kernel function addresses to custom
  overrides. Later in Ambient.Verifier.SymbolicExecution.lookupFunction, the
  functionKernelAddrMapping is consulted first before trying to resolve a
  function address to a function name in a binary.

  (Aside: this is not the only possible way of doing this. Instead of having
  a separate mapping on the side, we could also take the Macaw-loaded binary
  and manually inject the relevant function addresses into its Memory. While
  this would have the benefit of not needing any special cases in
  lookupFunction, it has the downside of being somewhat tricky to implement,
  so we do not take this approach currently.)

* aarch32LinuxFunctionABI defines a custom override for __kuser_get_tls in its
  functionKernelAddrMapping. The override simply returns the value stored in
  the TLS global variable that was initialized earlier. At present, this will
  always return the same symbolic value, but this could change in the future if
  we model the __ARM_NR_set_tls syscall.
-}
