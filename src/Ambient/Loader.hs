{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Ambient.Loader (
    withBinary
  ) where

import qualified Control.Monad.Catch as CMC
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
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
import qualified PE.Parser as PE

import qualified Ambient.Exception as AE
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
-- NOTE: We are currently fixing the memory model here. We will almost certainly
-- want to change that in the future (either to another fixed value or to make
-- it configurable)
withBinary
  :: (CMC.MonadThrow m)
  => FilePath
  -> BS.ByteString
  -> ( forall arch binFmt mem
      . (DMB.BinaryLoader arch binFmt, 16 <= DMC.ArchAddrWidth arch, DMS.SymArchConstraints arch, mem ~ DMS.LLVMMemory)
     => DMA.ArchitectureInfo arch
     -> DMS.GenArchVals mem arch
     -> AS.SyscallABI arch
     -> DMB.LoadedBinary arch binFmt
     -> m a)
  -> m a
withBinary name bytes k =
  case DE.decodeElfHeaderInfo bytes of
    Right (DE.SomeElf ehi) -> do
      -- See Note [ELF Load Options]
      let hdr = DE.header ehi
      case (DE.headerMachine hdr, DE.headerClass hdr) of
        (DE.EM_X86_64, DE.ELFCLASS64)
          | Just archVals <- DMS.archVals (Proxy @DMX.X86_64) -> do
            lb :: DMB.LoadedBinary DMX.X86_64 (DE.ElfHeaderInfo 64)
               <- DMB.loadBinary MML.defaultLoadOptions ehi
            -- Here we capture all of the necessary constraints required by the
            -- callback and pass them down along with the architecture info
            k DMX.x86_64_linux_info archVals ASXL.x86_64LinuxSyscallABI lb
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
