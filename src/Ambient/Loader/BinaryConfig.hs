module Ambient.Loader.BinaryConfig
  ( BinaryConfig(..)
  , mainLoadedBinaryPath
  , LoadedBinaryPath(..)
  , lbpAddrSymMap
  ) where

import qualified Data.Text.Encoding as DTE
import qualified Data.Vector.NonEmpty as NEV
import qualified Data.Map.Strict as Map

import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified What4.FunctionName as WF

import qualified Ambient.Loader.Versioning as ALV

-- | All of the loaded binaries along with information about their file paths,
-- function symbols, and PLT stubs. Retrieving this information requires
-- functionality that is specific to a particular file format (e.g., ELF), so
-- this data type provides a place to store this information so that it can be
-- used without hard-coding a particular file format.
data BinaryConfig arch binFmt = BinaryConfig {
    bcBinaries :: NEV.NonEmptyVector (LoadedBinaryPath arch binFmt)
  -- ^ A vector of all loaded binaries, where the binary at index 0 is the main
  -- binary, index 1 is the first shared library, index 2 is the second shared
  -- library, and so on. See @Note [Address offsets for shared libraries]@
  -- in "Ambient.Loader.LoadOffset".

  , bcMainBinarySymbolMap :: Map.Map WF.FunctionName (DMM.MemWord (DMC.ArchAddrWidth arch))
  -- ^ Maps the function symbols of each entry point function in the
  -- 'mainBinary' to their addresses. This is used to determine the address of
  -- the starting entry point. See @Note [Incremental code discovery]@ in
  -- "Ambient.Extensions".

  , bcDynamicFuncSymbolMap :: Map.Map ALV.VersionedFunctionName (DMM.MemWord (DMC.ArchAddrWidth arch))
  -- ^ Maps the names of dynamic functions in each binary to their addresses.
  -- This is used to determine the address that a PLT stub should jump to.
  -- See @Note [Incremental code discovery]@ in "Ambient.Extensions".

  , bcPltStubs :: Map.Map (DMM.MemWord (DMC.ArchAddrWidth arch)) ALV.VersionedFunctionName
  -- ^ Maps the addresses of PLT stub in each binary and shared library to
  -- their corresponding function names. See @Note [PLT Stub Names]@ in
  -- "Ambient.ELF.Loader.PLTStubDetector".

  , bcGlobalVarAddrs :: Map.Map ALV.VersionedGlobalVarName (DMM.MemWord (DMC.ArchAddrWidth arch))
  -- ^ Maps the names of exported global variables in each binary to their
  -- addresses.  This is used to compute relocations in dynamically linked
  -- programs.

  , bcUnsuportedRelocations :: Map.Map (DMM.MemWord (DMC.ArchAddrWidth arch)) String
  -- ^ A mapping of unsupported relocations.  Maps addresses to the names of
  -- unsupported relocation types.  This allows the verifier to simulate
  -- programs containing unsupported relocation types and throw an error only
  -- if one of those relocations is read from.  This is a mapping to strings
  -- instead of relocation types because holding relocations in this map
  -- introduces IsRelocationType constraints that are difficult to fulfill
  -- when a function takes this underlying map but no binaries are loaded
  -- (such as when running crucible syntax override tests).
  }

-- | A loaded binary, along with the file path from which it was loaded and
-- a map of all its entry point functions.
data LoadedBinaryPath arch binFmt = LoadedBinaryPath {
    lbpBinary :: DMB.LoadedBinary arch binFmt
  -- ^ The loaded binary.

  , lbpPath :: FilePath
  -- ^ The path the 'lbpBinary' was loaded from.

  , lbpEntryPoints :: Map.Map (DMC.ArchSegmentOff arch) ALV.VersionedFunctionName
  -- This maps the entry point addresses in the 'lbpBinary' to their
  -- corresponding function names. This information is used for two purposes:
  --
  -- * Seeding code discovery (see "Ambient.Discovery"), and
  --
  -- * Looking up the names of functions in order to check if they have
  --   user-supplied overrides (see @Note [Incremental code discovery]@ in
  -- "Ambient.Extensions").

  -- TODO: Instead of threading around this information as a separate field in
  -- LoadedBinaryPath, we could retrieve it from the LoadedBinary directly by
  -- using the macaw-loader API. Unfortunately, macaw-loader only supports
  -- entry points from static symbol tables at present (see
  -- https://github.com/GaloisInc/macaw-loader/issues/12), so we would have to
  -- fix this issue upstream first.
  }

-- | Like 'lbpEntryPoints', but with the function names converted to
-- @ByteString@s. This conversion is needed so that the map can be passed to
-- code discovery–related functions in @macaw@.
lbpAddrSymMap :: LoadedBinaryPath arch binFmt -> DMD.AddrSymMap (DMC.ArchAddrWidth arch)
lbpAddrSymMap = fmap (DTE.encodeUtf8 . WF.functionName . ALV.versymSymbol) . lbpEntryPoints

-- | Retrieve the main binary—that is, the binary at index 0 of
-- 'bcBinaries'.
mainLoadedBinaryPath :: BinaryConfig arch binFmt -> LoadedBinaryPath arch binFmt
mainLoadedBinaryPath = NEV.head . bcBinaries
