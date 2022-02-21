{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.Syscall (
    Syscall(..)
  , SomeSyscall(..)
  , SyscallNumRepr(..)
  , SyscallFnHandle(..)
  , SyscallABI(..)
  , BuildSyscallABI(..)
  , buildExecveOverride
  , exitOverride
  , getppidOverride
  , buildReadOverride
  , buildWriteOverride
  , buildOpenOverride
  , buildCloseOverride
  ) where

import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Foldable as F
import qualified Data.Kind as Kind
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import           Data.String ( fromString )

import qualified Data.Macaw.CFG as DMC
import           Data.Macaw.X86.Symbolic ()
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.SimError as LCSS
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI

import           Ambient.Override
import qualified Ambient.EventTrace as AE
import qualified Ambient.Property.Definition as APD


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
              :: forall bak
               . LCB.IsSymBackend sym bak
              => bak
              -> Ctx.Assignment (LCS.RegEntry sym) args
              -- Arguments to syscall
              -> (forall rtp args' ret'. LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret))
          -- ^ Override capturing behavior of the syscall
          }

data SomeSyscall p sym ext =
  forall args ret . SomeSyscall (Syscall p sym args ext ret)

-- | A syscall number, paired with the types of the syscall's argument and
-- return registers for the benefit of admitting an 'PC.OrdF' instance.
data SyscallNumRepr :: (Ctx.Ctx LCT.CrucibleType, Ctx.Ctx LCT.CrucibleType) -> Kind.Type where
  SyscallNumRepr :: !(LCT.CtxRepr atps)
                 -> !(LCT.CtxRepr rtps)
                 -> !Integer
                 -> SyscallNumRepr '(atps, rtps)

-- NB: Strictly speaking, this is not a law-abiding TestEquality instance, as
-- testEquality can return Nothing even if the type indices are equal. See the
-- discussion at https://github.com/GaloisInc/parameterized-utils/issues/129.
-- We may want to replace this with an EqF instance in the future should the
-- superclasses of OrdF change.
instance PC.TestEquality SyscallNumRepr where
  testEquality (SyscallNumRepr atps1 rtps1 i1) (SyscallNumRepr atps2 rtps2 i2) = do
    LCT.Refl <- LCT.testEquality atps1 atps2
    LCT.Refl <- LCT.testEquality rtps1 rtps2
    if (i1 == i2) then Just LCT.Refl else Nothing

instance PC.OrdF SyscallNumRepr where
  compareF (SyscallNumRepr atps1 rtps1 i1) (SyscallNumRepr atps2 rtps2 i2) =
    PC.joinOrderingF (PC.compareF atps1 atps2) $
    PC.joinOrderingF (PC.compareF rtps1 rtps2) $
    PC.fromOrdering (compare i1 i2)

instance Show (SyscallNumRepr tps) where
  showsPrec _ (SyscallNumRepr _ _ i) = showString "SyscallNumRepr " . showsPrec 11 i
instance PC.ShowF SyscallNumRepr

-- | A 'LCF.FnHandle' for a syscall override.
data SyscallFnHandle :: (Ctx.Ctx LCT.CrucibleType, Ctx.Ctx LCT.CrucibleType) -> Kind.Type where
  SyscallFnHandle :: !(LCF.FnHandle atps (LCT.StructType rtps))
                  -> SyscallFnHandle '(atps, rtps)

deriving instance Show (SyscallFnHandle tps)
instance PC.ShowF SyscallFnHandle

matchCallExecveEvent :: APD.Transition -> Bool
matchCallExecveEvent t =
  case t of
    APD.IssuesExecveSyscall -> True
    _ -> False

-- | Override for the 'execve' system call.  Currently this override records
-- that it was invoked through the 'hitExec' global, then aborts.
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- 'execve' arguments.
callExecve :: ( LCB.IsSymBackend sym bak
              , LCLM.HasPtrWidth w
              )
           => AE.Properties
           -> bak
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callExecve props bak = do
  let sym = LCB.backendGetSym bak
  F.forM_ (AE.properties props) $ \(prop, traceGlobal) -> do
    t0 <- LCS.readGlobal traceGlobal
    t1 <- liftIO $ AE.recordEvent matchCallExecveEvent sym prop t0
    LCS.writeGlobal traceGlobal t1
  loc <- liftIO $ WI.getCurrentProgramLoc sym
  liftIO $ LCB.abortExecBecause $ LCB.EarlyExit loc

buildExecveOverride :: LCLM.HasPtrWidth w
                    => AE.Properties
                    -> Syscall p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType w)
buildExecveOverride props = Syscall {
    syscallName = fromString "execve"
  , syscallArgTypes = Ctx.empty
  , syscallReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , syscallOverride = \bak _args -> callExecve props bak
}

-- | Override for the 'exit' system call.
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- 'exit' argument.
callExit :: ( LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            )
         => bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ Exit code
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym LCT.UnitType)
callExit bak reg = liftIO $
  do let sym = LCB.backendGetSym bak
     ec <- LCLM.projectLLVM_bv bak (LCS.regValue reg)
     cond <- WI.bvEq sym ec =<< WI.bvLit sym ?ptrWidth (BVS.zero ?ptrWidth)
     -- If the argument is non-zero, throw an assertion failure. Otherwise,
     -- simply stop the current thread of execution.
     -- NOTE: In the future we may not want to distinguish between zero and
     -- non-zero exit codes.
     LCB.assert bak cond (LCSS.AssertFailureSimError
                          "Call to exit() with non-zero argument"
                          "")
     loc <- WI.getCurrentProgramLoc sym
     LCB.abortExecBecause $ LCB.EarlyExit loc

exitOverride :: forall p sym ext w
              . LCLM.HasPtrWidth w
             => Syscall p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) ext (LCT.UnitType)
exitOverride = Syscall {
    syscallName = fromString "exit"
  , syscallArgTypes = Ctx.empty Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
  , syscallReturnType = LCT.UnitRepr
  , syscallOverride = \bak args -> Ctx.uncurryAssignment (callExit bak) args
  }

-- | Override for the getppid(2) system call
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- 'getppid' return value.
callGetppid :: ( LCB.IsSymBackend sym bak
               , LCLM.HasPtrWidth w
               )
            => bak
            -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callGetppid bak = liftIO $ do
  let sym = LCB.backendGetSym bak
  -- The parent PID can change at any time due to reparenting, so this override
  -- always returns a new fresh value.
  symbolicResult <- WI.freshConstant sym
                                     (WI.safeSymbol "getppid")
                                     (WI.BaseBVRepr ?ptrWidth)
  LCLM.llvmPointer_bv sym symbolicResult

getppidOverride :: LCLM.HasPtrWidth w
                => Syscall p sym Ctx.EmptyCtx ext (LCLM.LLVMPointerType w)
getppidOverride = Syscall {
    syscallName = fromString "getppid"
  , syscallArgTypes = Ctx.empty
  , syscallReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , syscallOverride = \bak _args -> callGetppid bak
  }

-- | Override for the read(2) system call
--
-- See Note [Argument and Return Widths] for a discussion on the type of the
-- argument and return values.
callRead :: ( LCLM.HasLLVMAnn sym
            , LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            )
         => LCLS.LLVMFileSystem w
         -> LCS.GlobalVar LCLM.Mem
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ File descriptor to read from
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ Pointer to buffer to read into
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ Maximum number of bytes to read
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callRead fs memVar bak fd buf count = do
  let sym = LCB.backendGetSym bak
  -- Drop upper 32 bits from fd to create a 32 bit file descriptor
  fdReg <- liftIO $ ptrToBv32 bak ?ptrWidth fd

  -- Convert 'count' to a bitvector
  countBv <- liftIO $ LCLM.projectLLVM_bv bak (LCS.regValue count)
  let countReg = LCS.RegEntry (LCT.BVRepr ?ptrWidth) countBv

  -- Use llvm override for read
  resBv <- LCLS.callReadFileHandle bak memVar fs fdReg buf countReg

  liftIO $ LCLM.llvmPointer_bv sym resBv

-- | Given a filesystem and a memvar, construct an override for read(2)
buildReadOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> Syscall p
                             sym
                             (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w)
                             ext
                             (LCLM.LLVMPointerType w)
buildReadOverride fs memVar = Syscall {
    syscallName = fromString "read"
  , syscallArgTypes = Ctx.empty Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
                                Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
                                Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
  , syscallReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , syscallOverride =
      \bak args -> Ctx.uncurryAssignment (callRead fs memVar bak) args
  }

-- | The memory options used to configure the memory model for system calls
--
-- We use the most lax memory options possible, as machine code breaks many of
-- the C-level rules.
syscallMemOptions :: LCLM.MemOptions
syscallMemOptions = LCLM.laxPointerMemOptions

-- | Override for the write(2) system call
callWrite :: ( LCLM.HasLLVMAnn sym
             , LCB.IsSymBackend sym bak
             , LCLM.HasPtrWidth w
             )
          => LCLS.LLVMFileSystem w
          -> LCS.GlobalVar LCLM.Mem
          -> bak
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -- ^ File descriptor to write to
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -- ^ Pointer to buffer to read from
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -- ^ Number of bytes to write
          -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callWrite fs memVar bak fd buf count = do
  let sym = LCB.backendGetSym bak
  let ?memOpts = syscallMemOptions
  -- Drop upper 32 bits from fd to create a 32 bit file descriptor
  fdReg <- liftIO $ ptrToBv32 bak ?ptrWidth fd

  -- Convert 'count' to a bitvector
  countBv <- liftIO $ LCLM.projectLLVM_bv bak (LCS.regValue count)
  let countReg = LCS.RegEntry (LCT.BVRepr ?ptrWidth) countBv

  -- Use the llvm override for write
  resBv <- LCLS.callWriteFileHandle bak memVar fs fdReg buf countReg

  liftIO $ LCLM.llvmPointer_bv sym resBv

buildWriteOverride :: ( LCLM.HasLLVMAnn sym
                      , LCLM.HasPtrWidth w
                      )
                   => LCLS.LLVMFileSystem w
                   -> LCS.GlobalVar LCLM.Mem
                   -> Syscall p
                             sym
                             (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w
                                           Ctx.::> LCLM.LLVMPointerType w)
                             ext
                             (LCLM.LLVMPointerType w)
buildWriteOverride fs memVar = Syscall {
    syscallName = fromString "write"
  , syscallArgTypes = Ctx.empty Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
                                Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
                                Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
  , syscallReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , syscallOverride =
      \bak args -> Ctx.uncurryAssignment (callWrite fs memVar bak) args
  }

-- | Override for the open(2) system call
callOpen :: ( LCLM.HasLLVMAnn sym
            , LCB.IsSymBackend sym bak
            , LCLM.HasPtrWidth w
            )
         => LCLS.LLVMFileSystem w
         -> LCS.GlobalVar LCLM.Mem
         -> bak
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ File path to open
         -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
         -- ^ Flags to use when opening file
         -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callOpen fs memVar bak pathname flags = do
  let sym = LCB.backendGetSym bak
  let ?memOpts = syscallMemOptions
  -- Drop upper 32 bits from flags to create a 32 bit flags int
  flagsInt <- liftIO $ ptrToBv32 bak ?ptrWidth flags

  -- Use llvm override for open
  resBv <- LCLS.callOpenFile bak memVar fs pathname flagsInt

  -- Pad result out to 64 bit pointer
  liftIO $ bvToPtr sym resBv ?ptrWidth

buildOpenOverride :: ( LCLM.HasLLVMAnn sym
                     , LCLM.HasPtrWidth w
                     )
                  => LCLS.LLVMFileSystem w
                  -> LCS.GlobalVar LCLM.Mem
                  -> Syscall p
                            sym
                            (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                          Ctx.::> LCLM.LLVMPointerType w)
                            ext
                            (LCLM.LLVMPointerType w)
buildOpenOverride fs memVar = Syscall {
    syscallName = fromString "open"
  , syscallArgTypes = Ctx.empty Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
                                Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
  , syscallReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , syscallOverride =
      \bak args -> Ctx.uncurryAssignment (callOpen fs memVar bak) args
  }

-- | Override for the write(2) system call
callClose :: ( LCLM.HasLLVMAnn sym
             , LCB.IsSymBackend sym bak
             , LCLM.HasPtrWidth w
             )
          => LCLS.LLVMFileSystem w
          -> LCS.GlobalVar LCLM.Mem
          -> bak
          -> LCS.RegEntry sym (LCLM.LLVMPointerType w)
          -- ^ File descriptor to close
          -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType w))
callClose fs memVar bak fd = do
  let sym = LCB.backendGetSym bak
  let ?memOpts = syscallMemOptions
  -- Drop upper 32 bits from fd
  fdInt <- liftIO $ ptrToBv32 bak ?ptrWidth fd

  -- Use llvm override for close
  resBv <- LCLS.callCloseFile bak memVar fs fdInt

  -- Pad result out to 64 bit pointer
  liftIO $ bvToPtr sym resBv ?ptrWidth

buildCloseOverride :: ( LCLM.HasLLVMAnn sym
                      , LCLM.HasPtrWidth w
                      )
                   => LCLS.LLVMFileSystem w
                   -> LCS.GlobalVar LCLM.Mem
                   -> Syscall p
                             sym
                             (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                             ext
                             (LCLM.LLVMPointerType w)
buildCloseOverride fs memVar = Syscall {
    syscallName = fromString "close"
  , syscallArgTypes = Ctx.empty Ctx.:> (LCLM.LLVMPointerRepr ?ptrWidth)
  , syscallReturnType = LCLM.LLVMPointerRepr ?ptrWidth
  , syscallOverride =
      \bak args -> Ctx.uncurryAssignment (callClose fs memVar bak) args
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
data SyscallABI arch sym p =
  SyscallABI {
    -- Given a full register state, extract all of the arguments we need for
    -- the system call
    syscallArgumentRegisters
      :: forall bak args atps
       . (LCB.IsSymBackend sym bak)
      => bak
      -> LCT.CtxRepr atps
      -- Types of argument registers
      -> LCS.RegEntry sym (LCT.StructType atps)
      -- Argument register values
      -> LCT.CtxRepr args
      -- Types of syscall arguments
      -> IO (Ctx.Assignment (LCS.RegEntry sym) args)
      -- Syscall argument values

    -- Extract the syscall number from the register state
  , syscallNumberRegister
     :: forall bak atps
      . (LCB.IsSymBackend sym bak)
     => bak
     -> Ctx.Assignment LCT.TypeRepr atps
     -- Types of argument registers
     -> LCS.RegEntry sym (LCT.StructType atps)
     -- Argument register values
     -> IO (LCS.RegEntry sym (LCT.BVType (DMC.ArchAddrWidth arch)))
     -- Extracted syscall number

    -- Build an OverrideSim action with appropriate return register types from
    -- a given OverrideSim action
  , syscallReturnRegisters
     :: forall t ext r args rtps atps
      . LCT.TypeRepr t
     -- Syscall return type
     -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym t)
     -- OverrideSim action producing the syscall's return value
     -> LCT.CtxRepr atps
     -- Argument register types
     -> LCS.RegEntry sym (LCT.StructType atps)
     -- Argument register values from before syscall execution
     -> LCT.CtxRepr rtps
     -- Return register types
     -> LCS.OverrideSim p sym ext r args (LCT.StructType rtps) (LCS.RegValue sym (LCT.StructType rtps))
     -- OverrideSim action with return type matching system return register
     -- type

    -- A mapping from syscall numbers to overrides
  , syscallMapping
     :: forall ext
      . ( LCB.IsSymInterface sym
        , LCLM.HasLLVMAnn sym )
     => Map.Map Integer (SomeSyscall p sym ext)
  }

-- A function to construct a SyscallABI with file system and memory access, as
-- well as the ability to track whether an 'execve' call has been reached
newtype BuildSyscallABI arch sym p = BuildSyscallABI (
    LCLS.LLVMFileSystem (DMC.ArchAddrWidth arch)
    -- File system to use in syscalls
    -> LCS.GlobalVar LCLM.Mem
    -- MemVar for the execution
    -> AE.Properties
    -- The properties to be checked, along with their corresponding global traces
    -> SyscallABI arch sym p
  )

{- Note [Argument and Return Widths]

In the system call overrides we currently specify arguments and return types as
64 bit vectors.  However, for portability we may want to pass in the pointer
size as a repr.  On the other hand, many system calls logically restrict their
inputs and outputs to ranges smaller than those supported by register sized
values, so we also may want to more accurately capture those ranges.

-}
