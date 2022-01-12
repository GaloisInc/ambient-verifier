{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeApplications #-}

module Ambient.OverrideTester (
    ABI(..)
  , allABIs
  , TestInstance(..)
  , testOverrides
  ) where

import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Lumberjack as LJ

import qualified Data.Macaw.ARM as Macaw.AArch32
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.X86 as DMX
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM

import qualified Ambient.Diagnostic as AD
import qualified Ambient.FunctionOverride.AArch32.Linux as AFAL
import qualified Ambient.FunctionOverride.Extension as AFE
import qualified Ambient.FunctionOverride.X86_64.Linux as AFXL
import qualified Ambient.Solver as AS
import qualified Ambient.Timeout as AT
import qualified Ambient.Verifier.Prove as AVP

-- | ABIs supported by the test runner
data ABI = X86_64Linux | AArch32Linux
  deriving (Read, Show, Eq, Enum, Bounded)

-- | A list of all supported ABIs
allABIs :: [ABI]
allABIs = [minBound .. maxBound]

-- | A definition of the tests to be run
data TestInstance =
  TestInstance { tiSolver :: AS.Solver
               -- ^ The solver to use for path satisfiability checking and
               -- goals
               , tiFloatMode :: AS.FloatMode
               -- ^ The interpretation of floating point operations in SMT
               , tiOverrideDir :: FilePath
               -- ^ Path to the crucible syntax overrides directory
               , tiAbi :: ABI
               -- ^ ABI to use when loading crucible syntax functions
               }


-- | Run the override tests described by the given 'TestInstance'
testOverrides :: LJ.LogAction IO AD.Diagnostic
              -- ^ A logger to report diagnostic information to the caller
              -> TestInstance
              -- ^ A description of the test to run
              -> AT.Timeout
              -- ^ The solver timeout for each goal
              -> IO ()
testOverrides logAction tinst timeoutDuration = do
  hdlAlloc <- LCF.newHandleAllocator
  Some ng <- PN.newIONonceGenerator
  AS.withOnlineSolver (tiSolver tinst) (tiFloatMode tinst) ng $ \sym -> do
    let ?memOpts = LCLM.defaultMemOptions
    case tiAbi tinst of
      X86_64Linux ->
        case DMS.archVals (Proxy @DMX.X86_64) Nothing of
          Just archVals -> do
            let parserHooks = AFE.machineCodeParserHooks (Proxy @DMX.X86_64)
                                                         AFXL.x86_64LinuxTypes
            AFE.runOverrideTests logAction
                                 sym
                                 DMX.x86_64_linux_info
                                 archVals
                                 (tiOverrideDir tinst)
                                 ng
                                 hdlAlloc
                                 parserHooks
          Nothing -> error "Failed to build archVals for X86_64"
      AArch32Linux ->
        case DMS.archVals (Proxy @Macaw.AArch32.ARM) Nothing of
          Just archVals -> do
            let parserHooks = AFE.machineCodeParserHooks (Proxy @Macaw.AArch32.ARM)
                                                         AFAL.aarch32LinuxTypes
            AFE.runOverrideTests logAction
                                 sym
                                 Macaw.AArch32.arm_linux_info
                                 archVals
                                 (tiOverrideDir tinst)
                                 ng
                                 hdlAlloc
                                 parserHooks
          Nothing -> error "Failed to build archVals for AArch32"
    AVP.proveObligations logAction
                         sym
                         (AS.offlineSolver (tiSolver tinst))
                         timeoutDuration
    return ()
