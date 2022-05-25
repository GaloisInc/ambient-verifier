{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Ambient.FunctionOverride (
    FunctionOverride(..)
  , mkFunctionOverride
  , SomeFunctionOverride(..)
  , FunctionOverrideHandle
  , FunctionAddrLoc(..)
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

-- | A smart constructor for 'FunctionOverride' for the common case when:
--
-- * There are no global variables.
--
-- * The argument and result types are statically known.
mkFunctionOverride ::
  ( LCT.KnownRepr LCT.CtxRepr args
  , LCT.KnownRepr LCT.TypeRepr ret
  ) =>
  WF.FunctionName ->
  (forall bak solver scope st fs
     . ( LCB.IsSymBackend sym bak
       , sym ~ WE.ExprBuilder scope st fs
       , bak ~ LCBO.OnlineBackend solver scope st fs
       , WPO.OnlineSolver solver
       )
    => bak
    -> Ctx.Assignment (LCS.RegEntry sym) args
    -> (forall rtp args' ret'. LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret))) ->
  FunctionOverride p sym args ext ret
mkFunctionOverride name ov = FunctionOverride
  { functionName = name
  , functionGlobals = []
  , functionArgTypes = LCT.knownRepr
  , functionReturnType = LCT.knownRepr
  , functionOverride = ov
  }

data SomeFunctionOverride p sym ext =
  forall args ret . SomeFunctionOverride (FunctionOverride p sym args ext ret)

-- | A 'LCF.FnHandle' for a function override.
type FunctionOverrideHandle arch =
  LCF.FnHandle
    (LCT.EmptyCtx LCT.::> LCT.StructType (DMS.MacawCrucibleRegTypes arch))
    (LCT.StructType (DMS.MacawCrucibleRegTypes arch))

-- | Where is a function's address located?
data FunctionAddrLoc w
  = AddrInBinary (DMC.MemWord w) FilePath
    -- ^ The function address is located in a binary at the given 'FilePath'.
    --
    -- By convention, the 'FilePath' is the name of the binary, not its full
    -- path. This convention is convenient for a couple of reasons:
    --
    -- * When displaying the binary via the @list-overrides@ command, it
    --   results in more compact output.
    --
    -- * When specifying function address overrides in an @overrides.yaml@
    --   file, users need only write down the file name. We could,
    --   theoretically, require users to write down full paths, but this would
    --   (1) be more annoying and (2) make the @overrides.yaml@ file less
    --   portable.
  | AddrFromKernel (DMC.MemWord w)
    -- ^ The function address is provided by the kernel itself. See
    --   @Note [AArch32 and TLS]@ in "Ambient.FunctionOverride.AArch32.Linux"
    --   for one application of this.
  deriving (Eq, Ord, Show)

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

    -- A mapping of function addresses to overrides. This is utilized for two
    -- purposes:
    --
    -- * User-provided overrides at particular addresses, as specified in an
    --   @overrides.yaml@ file.
    --
    -- * Kernel-provided user helpers that are reachable from user space
    --   at fixed addresses in kernel memory. In particular, see
    --   Note [AArch32 and TLS] in Ambient.FunctionOverride.AArch32.Linux for
    --   how this is used to implement TLS for AArch32 binaries.
    --
    -- Note that if a function's address has an override in this map, that will
    -- always take precedence over any overrides for functions of the same name
    -- in 'functionNameMapping'.
  , functionAddrMapping
     :: Map.Map (FunctionAddrLoc (DMC.ArchAddrWidth arch))
                (SomeFunctionOverride p sym (DMS.MacawExt arch))

    -- A mapping from function names to overrides
  , functionNameMapping
     :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
     => Map.Map WF.FunctionName (SomeFunctionOverride p sym (DMS.MacawExt arch))
  }

-- A function to construct a FunctionABI with memory access
newtype BuildFunctionABI arch sym p = BuildFunctionABI (
       LCLS.LLVMFileSystem (DMC.ArchAddrWidth arch)
    -- File system to use in overrides
    -> AM.InitialMemory sym (DMC.ArchAddrWidth arch)
    -> Map.Map (DMC.MemWord (DMC.ArchAddrWidth arch)) String
    -- ^ Mapping from unsupported relocation addresses to the names of the
    -- unsupported relocation types.
    -> Map.Map (FunctionAddrLoc (DMC.ArchAddrWidth arch))
               (SomeFunctionOverride p sym (DMS.MacawExt arch))
    -- Overrides for functions at particular addresses
    -> [ SomeFunctionOverride p sym (DMS.MacawExt arch) ]
    -- Overrides for functions with particular names
    -> FunctionABI arch sym p
  )
