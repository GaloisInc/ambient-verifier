{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Ambient.Loader (
    withBinary
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as DT
import           GHC.TypeLits ( type (<=) )

import qualified Data.ElfEdit as DE
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import           Data.Macaw.BinaryLoader.X86 ()
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory.LoadCommon as MML
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.X86 as DMX
import           Data.Macaw.X86.Symbolic ()
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.CFG.Common as LCCC
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified PE.Parser as PE
import qualified What4.Interface as WI

import qualified Ambient.Exception as AE
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.X86_64.Linux as AFXL
import qualified Ambient.Memory as AM
import qualified Ambient.Memory.X86_64.Linux as AMXL
import qualified Ambient.Syscall as AS
import qualified Ambient.Syscall.X86_64.Linux as ASXL

-- | Load a bytestring as a binary image and associate it with a macaw
-- 'DMA.ArchitectureInfo' suitable for analyzing it
--
-- This currently supports ELF files and has some ability to recognize (but not
-- load) PE files.
--
-- In the continuation (third argument), one would invoke code discovery via
-- macaw.
--
-- Note that the @sym@ parameter is only required to avoid a proxy.
--
-- NOTE: We are currently fixing the memory model here. We will almost certainly
-- want to change that in the future (either to another fixed value or to make
-- it configurable)
withBinary
  :: (CMC.MonadThrow m, MonadIO m, sym ~ LCBO.OnlineBackend scope solver fs)
  => FilePath
  -> BS.ByteString
  -> LCF.HandleAllocator
  -> sym
  -> ( forall arch binFmt mem p
      . ( DMB.BinaryLoader arch binFmt
        , 16 <= DMC.ArchAddrWidth arch
        , DMS.SymArchConstraints arch
        , mem ~ DMS.LLVMMemory
        , p ~ DMS.MacawSimulatorState sym
        )
     => DMA.ArchitectureInfo arch
     -> DMS.GenArchVals mem arch
     -> AS.BuildSyscallABI arch sym p
     -> AF.BuildFunctionABI arch sym p
     -> LCSC.ParserHooks (DMS.MacawExt arch)
     -> AM.InitArchSpecificGlobals arch
     -> DMB.LoadedBinary arch binFmt
     -> m a)
  -> m a
withBinary name bytes hdlAlloc _sym k =
  case DE.decodeElfHeaderInfo bytes of
    Right (DE.SomeElf ehi) -> do
      -- See Note [ELF Load Options]
      let hdr = DE.header ehi
      case (DE.headerMachine hdr, DE.headerClass hdr) of
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
              lb :: DMB.LoadedBinary DMX.X86_64 (DE.ElfHeaderInfo 64)
                 <- DMB.loadBinary MML.defaultLoadOptions ehi
              -- Here we capture all of the necessary constraints required by the
              -- callback and pass them down along with the architecture info
              k DMX.x86_64_linux_info
                archVals
                ASXL.x86_64LinuxSyscallABI
                AFXL.x86_64LinuxFunctionABI
                (AFXL.x86_64LinuxParserHooks (Proxy @DMX.X86_64))
                (AMXL.x86_64LinuxInitGlobals fsbaseGlob gsbaseGlob)
                lb
            Nothing -> CMC.throwM (AE.UnsupportedELFArchitecture name DE.EM_X86_64 DE.ELFCLASS64)
        (machine, klass) -> CMC.throwM (AE.UnsupportedELFArchitecture name machine klass)
    Left _ ->
      case PE.decodePEHeaderInfo (BSL.fromStrict bytes) of
        Right (Some _) -> CMC.throwM (AE.UnsupportedPEArchitecture name)
        Left _ -> CMC.throwM (AE.UnsupportedBinaryFormat name)


{- Note [ELF Load Options]

We are using the default load options here. We may want to change the load
offset at some point, which would allow us to vary the address at which the
binary is loaded.  While we won't be able to make the load offset symbolic here,
it would allow us to test a few concrete cases.

-}
