{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Ambient.Loader (
    withBinary
  , symbolMap
  ) where

import qualified Control.Monad.Catch as CMC
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import           Data.Parameterized.Some ( Some(..) )

import qualified Data.ElfEdit as DE
import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.BinaryLoader as DMB
import           Data.Macaw.BinaryLoader.X86 ()
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory.LoadCommon as MML
import qualified Data.Macaw.X86 as DMX
import qualified PE.Parser as PE

import qualified Ambient.Exception as AE

symbolMap
  :: (DMB.BinaryLoader arch binFmt)
  => DMB.LoadedBinary arch binFmt
  -> DMD.AddrSymMap (DMC.ArchAddrWidth arch)
symbolMap = undefined

-- | Load a bytestring as a binary image and associate it with a macaw
-- 'DMA.ArchitectureInfo' suitable for analyzing it
--
-- This currently supports ELF files and has some ability to recognize (but not
-- load) PE files.
--
-- In the continuation (third argument), one would invoke code discovery via
-- macaw.
withBinary
  :: (CMC.MonadThrow m)
  => Maybe FilePath
  -> BS.ByteString
  -> (forall arch binFmt . (DMB.BinaryLoader arch binFmt) => DMA.ArchitectureInfo arch -> DMB.LoadedBinary arch binFmt -> m a)
  -> m a
withBinary name bytes k =
  case DE.decodeElfHeaderInfo bytes of
    Right (DE.SomeElf ehi) -> do
      -- See Note [ELF Load Options]
      let hdr = DE.header ehi
      case (DE.headerMachine hdr, DE.headerClass hdr) of
        (DE.EM_X86_64, DE.ELFCLASS64) -> do
          lb :: DMB.LoadedBinary DMX.X86_64 (DE.ElfHeaderInfo 64)
             <- DMB.loadBinary MML.defaultLoadOptions ehi
          k DMX.x86_64_linux_info lb
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
