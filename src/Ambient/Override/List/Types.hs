module Ambient.Override.List.Types
  ( OverrideLists(..)
  , mkOverrideLists
  ) where

import qualified Data.Map as Map

import qualified Data.Macaw.CFG as DMC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified What4.FunctionName as WF

import qualified Ambient.FunctionOverride as AF
import qualified Ambient.Syscall as ASy

data OverrideLists arch = OverrideLists
  { syscallOverrides :: [WF.FunctionName]
    -- ^ Overrides for system calls.
  , functionOverrides :: [WF.FunctionName]
    -- ^ Overrides for typical function calls (with the exception of
    -- kernel-related functions, as recorded in 'kernelFunctionOverrides').
  , kernelFunctionOverrides :: [(WF.FunctionName, DMC.MemWord (DMC.ArchAddrWidth arch))]
    -- ^ Overrides for special user-space functions that expose kernel-related
    -- functionality. Includes the address at which each function lives.
  } deriving Show

mkOverrideLists ::
     (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
  => ASy.SyscallABI arch sym p
  -> AF.FunctionABI arch sym p
  -> OverrideLists arch
mkOverrideLists syscallABI functionABI =
  OverrideLists
    { syscallOverrides =
        map (\(_, ASy.SomeSyscall (ASy.Syscall{ASy.syscallName = name})) ->
              name)
            (Map.toList (ASy.syscallOverrideMapping syscallABI))
    , functionOverrides =
        map (\(_, AF.SomeFunctionOverride (AF.FunctionOverride{AF.functionName = name})) ->
              name)
            (Map.toList (AF.functionNameMapping functionABI))
    , kernelFunctionOverrides =
        map (\(addr, AF.SomeFunctionOverride (AF.FunctionOverride{AF.functionName = name})) ->
              (name, addr))
            (Map.toList (AF.functionKernelAddrMapping functionABI))
    }
