{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Ambient.Loader (
    withBinary
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as DT
import qualified Data.Traversable.WithIndex as DTW
import qualified Data.Type.Equality as DTE
import           Data.Word ( Word64 )
import           GHC.TypeLits ( type (<=) )
import qualified System.FilePath as SF
import qualified System.FilePath.Glob as SFG

import qualified Data.ElfEdit as DE
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import           Data.Macaw.BinaryLoader.X86 ()
import           Data.Macaw.BinaryLoader.AArch32 ()
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.LoadCommon as MML
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.X86 as DMX
import           Data.Macaw.X86.Symbolic ()
import qualified Data.Macaw.ARM as Macaw.AArch32
import           Data.Macaw.AArch32.Symbolic ()
import qualified Lang.Crucible.CFG.Common as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified PE.Parser as PE
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI

import qualified Ambient.ABI as AA
import qualified Ambient.Exception as AE
import qualified Ambient.Extensions as AExt
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.Extension as AFE
import qualified Ambient.FunctionOverride.X86_64.Linux as AFXL
import qualified Ambient.FunctionOverride.AArch32.Linux as AFAL
import qualified Ambient.Memory as AM
import qualified Ambient.Memory.AArch32.Linux as AMAL
import qualified Ambient.Memory.X86_64.Linux as AMXL
import qualified Ambient.PLTStubDetector as AP
import qualified Ambient.Syscall as AS
import qualified Ambient.Syscall.AArch32.Linux as ASAL
import qualified Ambient.Syscall.X86_64.Linux as ASXL

-- | Read all @.so@ files in a directory.  Returns a list of pairs containing
-- @.so@ file names and the binary data those files contain.
readSharedObjects :: FilePath -> IO [(FilePath, BS.ByteString)]
readSharedObjects dir = do
  paths <- SFG.namesMatching (dir SF.</> "*.so*")
  mapM (\p -> (p,) <$> BS.readFile p) paths

-- | Load a bytestring as a binary image and associate it with a macaw
-- 'DMA.ArchitectureInfo' suitable for analyzing it
--
-- This currently supports ELF files and has some ability to recognize (but not
-- load) PE files.
--
-- In the continuation argument, one would invoke code discovery via macaw.
--
-- Note that the @sym@ parameter is only required to avoid a proxy.
--
-- NOTE: We are currently fixing the memory model here. We will almost certainly
-- want to change that in the future (either to another fixed value or to make
-- it configurable)
withBinary
  :: ( CMC.MonadThrow m
     , MonadIO m
     )
  => FilePath
  -- ^ Path to binary
  -> BS.ByteString
  -- ^ Binary contents
  -> Maybe FilePath
  -- ^ Path to directory containing @.so@ files
  -> LCF.HandleAllocator
  -> sym
  -> ( forall arch binFmt mem p w
      . ( DMB.BinaryLoader arch binFmt
        , 16 <= DMC.ArchAddrWidth arch
        , DMS.SymArchConstraints arch
        , mem ~ DMS.LLVMMemory
        , p ~ AExt.AmbientSimulatorState arch
        , w ~ DMC.RegAddrWidth (DMC.ArchReg arch)
        )
     => DMA.ArchitectureInfo arch
     -> DMS.GenArchVals mem arch
     -> AS.BuildSyscallABI arch sym p
     -> AF.BuildFunctionABI arch sym p
     -> LCSC.ParserHooks (DMS.MacawExt arch)
     -> AM.InitArchSpecificGlobals arch
     -> Map.Map (DMM.MemWord w) WF.FunctionName
     -> DMB.LoadedBinary arch binFmt
     -- ^ Binary loaded from 'bytes'
     -> [DMB.LoadedBinary arch binFmt]
     -- ^ Loaded shared object files
     -> m a)
  -> m a
withBinary name bytes sharedObjectDir hdlAlloc _sym k = do
  let ?memOpts = LCLM.laxPointerMemOptions
  case DE.decodeElfHeaderInfo bytes of
    Right (DE.SomeElf ehi) -> do
      -- See Note [ELF Load Options]
      let hdr = DE.header ehi
      let hdrMachine = DE.headerMachine hdr
      let hdrClass = DE.headerClass hdr
      let options = MML.defaultLoadOptions
      sharedObjectBytes <- liftIO $
        maybe (return []) readSharedObjects sharedObjectDir
      case (hdrMachine, hdrClass) of
        (DE.EM_X86_64, DE.ELFCLASS64) -> do
          fsbaseGlob <- liftIO $
            LCCC.freshGlobalVar hdlAlloc
                                (DT.pack "fsbase")
                                (LCLM.LLVMPointerRepr (WI.knownNat @64))
          gsbaseGlob <- liftIO $
            LCCC.freshGlobalVar hdlAlloc
                                (DT.pack "gsbase")
                                (LCLM.LLVMPointerRepr (WI.knownNat @64))
          let extOverride = AMXL.x86_64LinuxStmtExtensionOverride fsbaseGlob
                                                                  gsbaseGlob
          let mArchVals = DMS.archVals (Proxy @DMX.X86_64) (Just extOverride)
          case mArchVals of
            Just archVals -> do
              (lb, sos, headers) <-
                loadBinaries options ehi hdrMachine hdrClass sharedObjectBytes
              -- Here we capture all of the necessary constraints required by the
              -- callback and pass them down along with the architecture info
              k DMX.x86_64_linux_info
                archVals
                ASXL.x86_64LinuxSyscallABI
                AFXL.x86_64LinuxFunctionABI
                (AFE.machineCodeParserHooks (Proxy @DMX.X86_64)
                                            AFXL.x86_64LinuxTypes)
                (AMXL.x86_64LinuxInitGlobals fsbaseGlob gsbaseGlob)
                (AP.pltStubSymbols AA.X86_64Linux
                                   (Proxy @DE.X86_64_RelocationType)
                                   headers)
                lb
                sos
            Nothing -> CMC.throwM (AE.UnsupportedELFArchitecture name DE.EM_X86_64 DE.ELFCLASS64)
        (DE.EM_ARM, DE.ELFCLASS32) -> do
          tlsGlob <- liftIO $
            LCCC.freshGlobalVar hdlAlloc
                                (DT.pack "tls")
                                (LCLM.LLVMPointerRepr (WI.knownNat @32))
          let extOverride = AMAL.aarch32LinuxStmtExtensionOverride
          case DMS.archVals (Proxy @Macaw.AArch32.ARM) (Just extOverride) of
            Just archVals -> do
              (lb, sos, headers) <-
                loadBinaries options ehi hdrMachine hdrClass sharedObjectBytes
              k Macaw.AArch32.arm_linux_info
                archVals
                ASAL.aarch32LinuxSyscallABI
                (AFAL.aarch32LinuxFunctionABI tlsGlob)
                (AFE.machineCodeParserHooks (Proxy @Macaw.AArch32.ARM)
                                            AFAL.aarch32LinuxTypes)
                (AMAL.aarch32LinuxInitGlobals tlsGlob)
                (AP.pltStubSymbols AA.AArch32Linux
                                   (Proxy @DE.ARM32_RelocationType)
                                   headers)
                lb
                sos
            Nothing -> CMC.throwM (AE.UnsupportedELFArchitecture name DE.EM_ARM DE.ELFCLASS32)
        (machine, klass) -> CMC.throwM (AE.UnsupportedELFArchitecture name machine klass)
    Left _ -> throwDecodeFailure name bytes
  where
    -- Load the main binary and any shared objects
    loadBinaries options ehi hdrMachine hdrClass sharedObjectBytes = do
      lb <- DMB.loadBinary options ehi
      soInfos <- DTW.itraverse (loadSharedObject hdrMachine hdrClass)
                               sharedObjectBytes
      let (sos, soHeaders) = unzip soInfos
      let headers = (ehi, options) : soHeaders
      return (lb, sos, headers)

    loadSharedObject :: forall arch m w
                      . ( DMB.BinaryLoader arch (DE.ElfHeaderInfo w)
                        , CMC.MonadThrow m )
                     => DE.ElfMachine
                     -> DE.ElfClass w
                     -> Int
                     -> (FilePath, BS.ByteString)
                     -> m ( DMB.LoadedBinary arch (DE.ElfHeaderInfo w)
                          , (DE.ElfHeaderInfo w, MML.LoadOptions) )
    loadSharedObject expectedHeaderMachine expectedHeaderClass index (soName, soBytes) =
      case DE.decodeElfHeaderInfo soBytes of
        Right (DE.SomeElf ehi) -> do
          let hdr = DE.header ehi
          if DE.headerMachine hdr == expectedHeaderMachine
          then
            case DTE.testEquality (DE.headerClass hdr) expectedHeaderClass of
              Just DTE.Refl -> do
                let options = indexToLoadOptions (fromIntegral (index + 1))
                lb <- DMB.loadBinary options ehi
                return (lb, (ehi, options))
              _ -> CMC.throwM (AE.SoMismatchedElfClass (DE.headerClass hdr)
                                                       expectedHeaderClass)
          else CMC.throwM (AE.SoMismatchedElfMachine (DE.headerMachine hdr)
                                                     expectedHeaderMachine)
        Left _ -> throwDecodeFailure soName soBytes

    throwDecodeFailure elfName elfBytes =
      case PE.decodePEHeaderInfo (BSL.fromStrict elfBytes) of
        Right (Some _) -> CMC.throwM (AE.UnsupportedPEArchitecture elfName)
        Left _ -> CMC.throwM (AE.UnsupportedBinaryFormat elfName)

-- | Given an index value, constructs an 'MML.LoadOptions' for the appropriate
-- offset to load a shared object at.
indexToLoadOptions :: Word64 -> MML.LoadOptions
indexToLoadOptions index =
  -- NOTE: This load offset calculation is safe so long as all binaries are
  -- under 256MB.  It seems likely that something else in the verifier would
  -- fail before binaries reach that size.
  -- NOTE: On 32-bit architectures 'index' values of 16 or higher will cause
  -- the offset to reach inaccessible values.  Macaw throws an exception in
  -- this case.  If this occurs in practice we will need to reduce the offset
  -- multiplier to something smaller (the trade-off is that the maximum
  -- allowable library size will also decrease).
  MML.LoadOptions { MML.loadOffset = Just $ 0x10000000 * index }

{- Note [ELF Load Options]

We are using the default load options here. We may want to change the load
offset at some point, which would allow us to vary the address at which the
binary is loaded.  While we won't be able to make the load offset symbolic here,
it would allow us to test a few concrete cases.

-}
