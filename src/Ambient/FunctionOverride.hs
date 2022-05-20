{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.FunctionOverride (
    FunctionOverride(..)
  , SomeFunctionOverride(..)
  , FunctionOverrideHandle
  , FunctionABI(..)
  , BuildFunctionABI(..)
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Protocol.Online as WPO

import qualified Ambient.Memory as AM

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
                       :: forall bak solver scope st fs
                        . ( LCB.IsSymBackend sym bak
                          , sym ~ WE.ExprBuilder scope st fs
                          , bak ~ LCBO.OnlineBackend solver scope st fs
                          , WPO.OnlineSolver solver
                          )
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

    -- The two registers used to store arguments in an
    -- @int main(int argc, char *argv[])@ function.
  , functionMainArgumentRegisters
      :: ( DMC.ArchReg arch (DMT.BVType (DMC.ArchAddrWidth arch))
         , DMC.ArchReg arch (DMT.BVType (DMC.ArchAddrWidth arch))
         )

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
       LCLS.LLVMFileSystem (DMC.ArchAddrWidth arch)
    -- File system to use in overrides
    -> AM.InitialMemory sym (DMC.ArchAddrWidth arch)
    -> Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch)) String
    -- ^ Mapping from unsupported relocation addresses to the names of the
    -- unsupported relocation types.
    -> [ SomeFunctionOverride p sym (DMS.MacawExt arch) ]
    -- Additional overrides
    -> Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch))
               (SomeFunctionOverride p sym (DMS.MacawExt arch))
    -- Overrides for kernel-provided user helpers
    -> FunctionABI arch sym p
  )
