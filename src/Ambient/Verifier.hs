{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | The main entry point of the AMBIENT binary verifier
module Ambient.Verifier (
    ProgramInstance(..)
  , verify
  ) where

import           Control.Lens ( (^.) )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Some ( Some(..) )
import           GHC.Stack ( HasCallStack )
import qualified Lumberjack as LJ

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Discovery as ADi
import qualified Ambient.Exception as AE
import qualified Ambient.Lift as ALi
import qualified Ambient.Loader as AL

-- | A definition of the initial state of a program to be verified
--
-- Currently, this just defines the /concrete/ initial state of the
-- program. This will be extended later to support explicitly symbolic initial
-- states.
data ProgramInstance =
  ProgramInstance { piPath :: FilePath
                  -- ^ The path to the binary on disk (or a synthetic name)
                  , piBinary :: BS.ByteString
                  -- ^ The contents of the binary to verify, which will be
                  -- parsed and lifted into the verification IR
                  , piStdin :: Maybe BS.ByteString
                  -- ^ The contents to be passed to the program via standard
                  -- input, which can be empty
                  , piCommandLineArguments :: [BS.ByteString]
                  -- ^ The command line arguments to pass to the program
                  --
                  -- The caller should ensure that this includes argv[0] (the
                  -- program name)
                  --
                  -- Note that the command line UI can take textual arguments;
                  -- the real arguments here are 'BS.ByteString's because that
                  -- is how they must be represented in the memory model.
                  }
  deriving (Show)

-- | Retrieve the named function (in its 'DMD.DiscoveryFunInfo' form) from the code
-- discovery information
--
-- If the symbol is not present in the binary, or if discovery was unable to
-- find it, this function will throw exceptions.
getNamedFunction
  :: ( CMC.MonadThrow m
     , DMM.MemWidth (DMC.ArchAddrWidth arch)
     )
  => DMD.DiscoveryState arch
  -- ^ A computed discovery state
  -> String
  -- ^ The name of the function to retrieve
  -> m (Some (DMD.DiscoveryFunInfo arch))
getNamedFunction discoveryState fname = do
  let entryPointName = BSC.pack fname
  let symbolNamesToAddrs = Map.fromList [ (name, addr)
                                        | (addr, name) <- Map.toList (DMD.symbolNames discoveryState)
                                        ]
  case Map.lookup entryPointName symbolNamesToAddrs of
    Nothing -> CMC.throwM (AE.MissingExpectedSymbol entryPointName)
    Just entryAddr
      | Just dfi <- Map.lookup entryAddr (discoveryState ^. DMD.funInfo) -> return dfi
      | otherwise -> CMC.throwM (AE.MissingExpectedFunction (Just entryPointName) entryAddr)

-- | Verify that the given 'ProgramInstance' terminates (with the given input)
-- without raising an error
verify
  :: (MonadIO m, CMC.MonadThrow m, HasCallStack)
  => LJ.LogAction IO AD.Diagnostic
  -- ^ A logger to report diagnostic information to the caller
  -> ProgramInstance
  -- ^ A description of the program (and its configuration) to verify
  -> m ()
verify logAction pinst = do
  -- Load up the binary, which existentially introduces the architecture of the
  -- binary in the context of the continuation
  AL.withBinary (piPath pinst) (piBinary pinst) $ \archInfo symArchFuns loadedBinary -> do
    discoveryState <- ADi.discoverFunctions logAction archInfo loadedBinary
    -- See Note [Entry Point] for more details
    Some discoveredEntry <- getNamedFunction discoveryState "main"
    hdlAlloc <- liftIO LCF.newHandleAllocator
    LCCC.SomeCFG cfg0 <- ALi.liftDiscoveredFunction hdlAlloc (piPath pinst) symArchFuns discoveredEntry
    return ()

{- Note [Entry Point]

Right now, we are starting verification from ~main~ instead of ~_start~. Macaw
can have trouble analyzing from ~_start~, especially in stripped binaries,
because the startup sequence passes function pointers indirectly to kick off
main.

This can be fixed up later by lazily re-running discovery as we identify new
entry points (i.e., by demand as they are jumped to through function pointers).

The other complexity is that there is substantial state that must be reasonably
concrete for symbolic execution from ~_start~ to terminate. We will eventually
fill all of that in.

-}
