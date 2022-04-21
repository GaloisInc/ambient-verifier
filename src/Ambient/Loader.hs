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
import qualified Data.List.NonEmpty as NEL
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as DT
import qualified Data.Traversable.WithIndex as DTW
import qualified Data.Type.Equality as DTE
import qualified Data.Vector.NonEmpty as NEV
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
import qualified What4.Interface as WI

import qualified Ambient.ABI as AA
import qualified Ambient.Exception as AE
import qualified Ambient.Extensions as AExt
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.Extension as AFE
import qualified Ambient.FunctionOverride.X86_64.Linux as AFXL
import qualified Ambient.FunctionOverride.AArch32.Linux as AFAL
import qualified Ambient.Loader.BinaryConfig as ALB
import qualified Ambient.Loader.ELF.Symbols as ALES
import qualified Ambient.Loader.ELF.Symbols.AArch32 as ALESA
import qualified Ambient.Loader.ELF.PLTStubDetector as ALEP
import qualified Ambient.Loader.LoadOptions as ALL
import qualified Ambient.Loader.Versioning as ALV
import qualified Ambient.Memory as AM
import qualified Ambient.Memory.AArch32.Linux as AMAL
import qualified Ambient.Memory.X86_64.Linux as AMXL
import qualified Ambient.Syscall as AS
import qualified Ambient.Syscall.AArch32.Linux as ASAL
import qualified Ambient.Syscall.X86_64.Linux as ASXL

-- | Read all @.so@ files in a directory.  Returns a list of pairs containing
-- @.so@ file names and the binary data those files contain.
readSharedObjects :: FilePath -> IO [(FilePath, BS.ByteString)]
readSharedObjects dir = do
  paths <- SFG.glob (dir SF.</> "*.so*")
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
  :: forall m sym a
   . ( CMC.MonadThrow m
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
        , p ~ AExt.AmbientSimulatorState sym arch
        , w ~ DMC.RegAddrWidth (DMC.ArchReg arch)
        )
     => DMA.ArchitectureInfo arch
     -> DMS.GenArchVals mem arch
     -> AS.BuildSyscallABI arch sym p
     -> AF.BuildFunctionABI arch sym p
     -> LCSC.ParserHooks (DMS.MacawExt arch)
     -> AM.InitArchSpecificGlobals arch
     -> Int
     -- ^ Total number of bytes loaded (includes shared libraries).
     -> ALB.BinaryConfig arch binFmt
     -- ^ Information about the loaded binaries
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
      let soFilePaths = fmap fst sharedObjectBytes
      let totalBytes = BS.length bytes
                     + sum [BS.length x | (_, x) <- sharedObjectBytes]
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
              bins <- loadBinaries options ehi hdrMachine hdrClass sharedObjectBytes
              binConf <- mkElfBinConf AA.X86_64Linux
                                      (Proxy @DE.X86_64_RelocationType)
                                      soFilePaths bins
                                      -- NOTE: We do not currently support
                                      -- relocations on X86 so we pass in empty
                                      -- maps for the relocation structures
                                      -- (see ticket #98).
                                      Map.empty
                                      Map.empty
              -- Here we capture all of the necessary constraints required by the
              -- callback and pass them down along with the architecture info
              k DMX.x86_64_linux_info
                archVals
                ASXL.x86_64LinuxSyscallABI
                AFXL.x86_64LinuxFunctionABI
                (AFE.machineCodeParserHooks (Proxy @DMX.X86_64)
                                            AFXL.x86_64LinuxTypes)
                (AMXL.x86_64LinuxInitGlobals fsbaseGlob gsbaseGlob)
                totalBytes
                binConf
            Nothing -> CMC.throwM (AE.UnsupportedELFArchitecture name DE.EM_X86_64 DE.ELFCLASS64)
        (DE.EM_ARM, DE.ELFCLASS32) -> do
          tlsGlob <- liftIO $
            LCCC.freshGlobalVar hdlAlloc
                                (DT.pack "tls")
                                (LCLM.LLVMPointerRepr (WI.knownNat @32))
          let extOverride = AMAL.aarch32LinuxStmtExtensionOverride
          case DMS.archVals (Proxy @Macaw.AArch32.ARM) (Just extOverride) of
            Just archVals -> do
              bins <- loadBinaries options ehi hdrMachine hdrClass sharedObjectBytes
              unsupportedRels <- liftIO $ ALESA.elfAarch32UnsupportedRels bins
              dynGlobSymMap <- liftIO $ ALES.elfDynamicGlobalSymbolMap bins
              binConf <- mkElfBinConf AA.AArch32Linux
                                      (Proxy @DE.ARM32_RelocationType)
                                      soFilePaths bins
                                      dynGlobSymMap
                                      unsupportedRels
              k Macaw.AArch32.arm_linux_info
                archVals
                ASAL.aarch32LinuxSyscallABI
                (AFAL.aarch32LinuxFunctionABI tlsGlob)
                (AFE.machineCodeParserHooks (Proxy @Macaw.AArch32.ARM)
                                            AFAL.aarch32LinuxTypes)
                (AMAL.aarch32LinuxInitGlobals tlsGlob)
                totalBytes
                binConf
            Nothing -> CMC.throwM (AE.UnsupportedELFArchitecture name DE.EM_ARM DE.ELFCLASS32)
        (machine, klass) -> CMC.throwM (AE.UnsupportedELFArchitecture name machine klass)
    Left _ -> throwDecodeFailure name bytes
  where
    -- Load the main binary and any shared objects
    loadBinaries
      :: (DMB.BinaryLoader arch (DE.ElfHeaderInfo w))
      => MML.LoadOptions
      -> DE.ElfHeaderInfo w
      -> DE.ElfMachine
      -> DE.ElfClass w
      -> [(FilePath, BS.ByteString)]
      -> m (NEV.NonEmptyVector (DMB.LoadedBinary arch (DE.ElfHeaderInfo w)))
    loadBinaries options ehi hdrMachine hdrClass sharedObjectBytes = do
      lb <- DMB.loadBinary options ehi
      sos <- DTW.itraverse (loadSharedObject hdrMachine hdrClass)
                           sharedObjectBytes
      pure $ NEV.fromNonEmpty $ lb NEL.:| sos

    loadSharedObject :: forall arch w
                      . ( DMB.BinaryLoader arch (DE.ElfHeaderInfo w) )
                     => DE.ElfMachine
                     -> DE.ElfClass w
                     -> Int
                     -> (FilePath, BS.ByteString)
                     -> m (DMB.LoadedBinary arch (DE.ElfHeaderInfo w))
    loadSharedObject expectedHeaderMachine expectedHeaderClass index (soName, soBytes) =
      case DE.decodeElfHeaderInfo soBytes of
        Right (DE.SomeElf ehi) -> do
          let hdr = DE.header ehi
          if DE.headerMachine hdr == expectedHeaderMachine
          then
            case DTE.testEquality (DE.headerClass hdr) expectedHeaderClass of
              Just DTE.Refl -> do
                let options = ALL.indexToLoadOptions (fromIntegral (index + 1))
                DMB.loadBinary options ehi
              _ -> CMC.throwM (AE.SoMismatchedElfClass (DE.headerClass hdr)
                                                       expectedHeaderClass)
          else CMC.throwM (AE.SoMismatchedElfMachine (DE.headerMachine hdr)
                                                     expectedHeaderMachine)
        Left _ -> throwDecodeFailure soName soBytes

    -- Construct a BinaryConfig for an ELF file.
    mkElfBinConf ::
      forall arch binFmt w proxy reloc.
      ( binFmt ~ DE.ElfHeaderInfo (DMC.ArchAddrWidth arch)
      , w ~ DMC.ArchAddrWidth arch
      , w ~ DE.RelocationWidth reloc
      , Integral (DE.ElfWordType w)
      , DE.IsRelocationType reloc
      , DMM.MemWidth w
      ) =>
      AA.ABI ->
      proxy reloc ->
      -- ^ The relocation type to use when detecting PLT stubs
      [FilePath] ->
      -- ^ The paths of the loaded shared libraries
      NEV.NonEmptyVector (DMB.LoadedBinary arch binFmt) ->
      -- ^ All loaded binaries, including shared libraries
      Map.Map ALV.VersionedGlobalVarName (DMM.MemWord (DMC.ArchAddrWidth arch)) ->
      -- ^ Mapping from exported global variable names to addresses
      Map.Map (DMM.MemWord (DMC.ArchAddrWidth arch)) String ->
      -- ^ Unsupported relocations.  Mapping from addresses to names of
      -- unsupported relocation types.
      m (ALB.BinaryConfig arch binFmt)
    mkElfBinConf abi proxyReloc soFilePaths bins globals unsupportedRels = do
      let loadedBinaryPaths =
            NEV.zipWith
              (\bin path ->
                ALB.LoadedBinaryPath
                  { ALB.lbpBinary = bin
                  , ALB.lbpPath = path
                  , ALB.lbpEntryPoints = ALES.elfEntryPointAddrMap bin
                  })
              bins
              (NEV.fromNonEmpty (name NEL.:| soFilePaths))
      dynFuncSymMap <- liftIO $ ALES.elfDynamicFuncSymbolMap bins
      return ALB.BinaryConfig
        { ALB.bcBinaries = loadedBinaryPaths
        , ALB.bcMainBinarySymbolMap = ALES.elfEntryPointSymbolMap (NEV.head bins)
        , ALB.bcDynamicFuncSymbolMap = dynFuncSymMap
        , ALB.bcPltStubs = ALEP.pltStubSymbols abi proxyReloc bins
        , ALB.bcGlobalVarAddrs = globals
        , ALB.bcUnsuportedRelocations = unsupportedRels
        }

    throwDecodeFailure elfName elfBytes =
      case PE.decodePEHeaderInfo (BSL.fromStrict elfBytes) of
        Right (Some _) -> CMC.throwM (AE.UnsupportedPEArchitecture elfName)
        Left _ -> CMC.throwM (AE.UnsupportedBinaryFormat elfName)

{- Note [ELF Load Options]

We are using the default load options here. We may want to change the load
offset at some point, which would allow us to vary the address at which the
binary is loaded.  While we won't be able to make the load offset symbolic here,
it would allow us to test a few concrete cases.

-}
