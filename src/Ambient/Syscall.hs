{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.Syscall (
    Syscall(..)
  , SomeSyscall(..)
  , SyscallABI(..)
  , BuildSyscallABI(..)
  , exitOverride
  , getppidOverride
  , buildReadOverride
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Map.Strict as Map
import           Data.String ( fromString )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Vector as Vector

import qualified Data.Macaw.CFG as DMC
import           Data.Macaw.X86.Symbolic ()
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.Intrinsics as LCLI
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.SimError as LCSS
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI

-------------------------------------------------------------------------------
-- System Call Overrides
-------------------------------------------------------------------------------

-- | Syscall captures an override and type information about how to call it
data Syscall p sym args ext ret =
  Syscall { syscallName :: WF.FunctionName
          -- ^ Name of the syscall
          , syscallArgTypes :: LCT.CtxRepr args
          -- ^ Types of the arguments to the syscall
          , syscallReturnType :: LCT.TypeRepr ret
          -- ^ Return type of the syscall
          , syscallOverride
              :: sym
              -> Ctx.Assignment (LCS.RegEntry sym) args
              -- ^ Arguments to syscall
              -> (forall rtp args' ret'. LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret))
          -- ^ Override capturing behavior of the syscall
          }

data SomeSyscall p sym ext =
  forall args ret . SomeSyscall (Syscall p sym args ext ret)

-- | Override for the 'exit' system call.
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- 'exit' argument.
callExit :: (LCB.IsSymInterface sym)
         => sym
         -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
         -- ^ Exit code
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym LCT.UnitType)
callExit sym reg = liftIO $
  do ec <- LCLM.projectLLVM_bv sym (LCS.regValue reg)
     cond <- WI.bvEq sym ec =<< WI.bvLit sym WI.knownNat (BVS.zero WI.knownNat)
     -- If the argument is non-zero, throw an assertion failure. Otherwise,
     -- simply stop the current thread of execution.
     -- NOTE: In the future we may not want to distinguish between zero and
     -- non-zero exit codes.
     LCB.assert sym cond (LCSS.AssertFailureSimError
                          "Call to exit() with non-zero argument"
                          "")
     loc <- WI.getCurrentProgramLoc sym
     LCB.abortExecBecause $ LCB.EarlyExit loc

exitOverride :: forall p sym ext
              . (LCB.IsSymInterface sym)
             => Syscall p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64) ext (LCT.UnitType)
exitOverride = Syscall {
    syscallName = fromString "exit"
  , syscallArgTypes = Ctx.empty Ctx.:> (LCLM.LLVMPointerRepr (WI.knownNat @64))
  , syscallReturnType = LCT.UnitRepr
  , syscallOverride = (\sym args -> Ctx.uncurryAssignment (callExit sym) args)
  }

-- | Override for the getppid(2) system call
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- 'getppid' return value.
callGetppid :: (LCB.IsSymInterface sym)
            => sym
            -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
callGetppid sym = liftIO $ do
  -- The parent PID can change at any time due to reparenting, so this override
  -- always returns a new fresh value.
  symbolicResult <- WI.freshConstant sym
                                     (WI.safeSymbol "getppid")
                                     (WI.BaseBVRepr (WI.knownNat @64))
  LCLM.llvmPointer_bv sym symbolicResult

getppidOverride :: (LCB.IsSymInterface sym)
                => Syscall p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType 64)
getppidOverride = Syscall {
    syscallName = fromString "getppid"
  , syscallArgTypes = Ctx.empty
  , syscallReturnType = LCLM.LLVMPointerRepr (WI.knownNat @64)
  , syscallOverride = (\sym _args -> callGetppid sym)
  }

-- | Override for the read(2) system call
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- argument and return values.
callRead :: ( LCLM.HasLLVMAnn sym
            , LCB.IsSymInterface sym )
         => LCLS.LLVMFileSystem 64
         -> LCS.GlobalVar LCLM.Mem
         -> sym
         -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
         -- ^ File descriptor to read from
         -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
         -- ^ Pointer to buffer to read into
         -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
         -- ^ Maximum number of bytes to read
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
callRead fs memVar sym fd buf count = do
  let ?ptrWidth = WI.knownRepr
  -- Drop upper 32 bits from fd to create a 32 bit file descriptor
  fd64Bv <- liftIO $ LCLM.projectLLVM_bv sym (LCS.regValue fd)
  fdSplit <- liftIO $ WI.bvSplitVector sym (WI.knownNat @2) (WI.knownNat @32) fd64Bv
  let fdReg = LCS.RegEntry LCT.knownRepr (Vector.elemAt (WI.knownNat @1) fdSplit)

  -- Convert 'count' to a bitvector
  countBv <- liftIO $ LCLM.projectLLVM_bv sym (LCS.regValue count)
  let countReg = LCS.RegEntry LCT.knownRepr countBv

  -- Use llvm override for read
  let readLlvmOv = LCLI.llvmOverride_def (LCLS.readFileHandle fs)
  resBv <- readLlvmOv memVar sym (Ctx.empty Ctx.:> fdReg Ctx.:> buf Ctx.:> countReg)

  liftIO $ LCLM.llvmPointer_bv sym resBv

-- | Given a filesystem and a memvar, construct an override for read(2)
buildReadOverride :: ( LCLM.HasLLVMAnn sym
                     , LCB.IsSymInterface sym )
                  => LCLS.LLVMFileSystem 64
                  -> LCS.GlobalVar LCLM.Mem
                  -> Syscall p
                             sym
                             (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                           Ctx.::> LCLM.LLVMPointerType 64
                                           Ctx.::> LCLM.LLVMPointerType 64)
                             ext
                             (LCLM.LLVMPointerType 64)
buildReadOverride fs memVar = Syscall {
    syscallName = fromString "read"
  , syscallArgTypes = Ctx.empty Ctx.:> (LCLM.LLVMPointerRepr (WI.knownNat @64))
                                Ctx.:> (LCLM.LLVMPointerRepr (WI.knownNat @64))
                                Ctx.:> (LCLM.LLVMPointerRepr (WI.knownNat @64))
  , syscallReturnType = LCLM.LLVMPointerRepr (WI.knownNat @64)
  , syscallOverride =
      \sym args -> Ctx.uncurryAssignment (callRead fs memVar sym) args
  }

-------------------------------------------------------------------------------
-- System Call ABI Specification
-------------------------------------------------------------------------------

-- Now we actually need to perform the architecture-specific mapping. We can
-- use the type-level information in the override signatures to help us (and
-- especially the type repr inside of the Syscall type)
--
-- Note that this is data rather than a class because there can be different
-- ABIs for a given architecture (e.g., Windows and Linux)
data SyscallABI arch =
  SyscallABI {
    -- Given a full register state, extract all of the arguments we need for
    -- the system call
    syscallArgumentRegisters
      :: forall args sym atps
       . (LCB.IsSymInterface sym)
      => LCT.CtxRepr atps
      -- ^ Types of argument registers
      -> LCS.RegEntry sym (LCT.StructType atps)
      -- ^ Argument register values
      -> LCT.CtxRepr args
      -- ^ Types of syscall arguments
      -> Ctx.Assignment (LCS.RegEntry sym) args
      -- ^ Syscall argument values

    -- Extract the syscall number from the register state
  , syscallNumberRegister
     :: forall sym atps
      . (LCB.IsSymInterface sym)
     => sym
     -> Ctx.Assignment LCT.TypeRepr atps
     -- ^ Types of argument registers
     -> LCS.RegEntry sym (LCT.StructType atps)
     -- ^ Argument register values
     -> IO (LCS.RegEntry sym (LCT.BVType (DMC.ArchAddrWidth arch)))
     -- ^ Extracted syscall number

    -- Build an OverrideSim action with appropriate return register types from
    -- a given OverrideSim action
  , syscallReturnRegisters
     :: forall t p sym ext r args rtps atps
      . LCT.TypeRepr t
     -- ^ Syscall return type
     -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym t)
     -- ^ OverrideSim action producing the syscall's return value
     -> LCT.CtxRepr atps
     -- ^ Argument register types
     -> LCS.RegEntry sym (LCT.StructType atps)
     -- ^ Argument register values from before syscall execution
     -> LCT.CtxRepr rtps
     -- ^ Return register types
     -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym (LCT.StructType rtps))
     -- ^ OverrideSim action with return type matching system return register
     -- type

    -- A mapping from syscall numbers to overrides
  , syscallMapping
     :: forall p sym ext
      . ( LCB.IsSymInterface sym
        , LCLM.HasLLVMAnn sym )
     => Map.Map Integer (SomeSyscall p sym ext)
  }

-- A function to construct a SyscallABI with file system and memory access
newtype BuildSyscallABI arch = BuildSyscallABI (
    LCLS.LLVMFileSystem (DMC.ArchAddrWidth arch)
    -> LCS.GlobalVar LCLM.Mem
    -> SyscallABI arch
  )

{- Note [Argument and Return Widths]

In the system call overrides we currently specify arguments and return types as
64 bit vectors.  However, for portability we may want to pass in the pointer
size as a repr.  On the other hand, many system calls logically restrict their
inputs and outputs to ranges smaller than those supported by register sized
values, so we also may want to more accurately capture those ranges.

-}
