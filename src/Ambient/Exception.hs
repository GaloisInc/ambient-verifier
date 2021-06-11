{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Ambient.Exception (
  AmbientException(..)
  ) where

import qualified Control.Exception as X
import qualified Data.ElfEdit as DE
import qualified Prettyprinter as PP

data AmbientException where
  -- | The given binary format is not supported
  --
  -- We don't necessarily know what it is, and we may not have a filename (if
  -- the verifier was just passed a bytestring with no filename)
  UnsupportedBinaryFormat :: Maybe FilePath -> AmbientException
  -- | The file was a valid ELF binary, but for an architecture that we do not support
  UnsupportedELFArchitecture :: Maybe FilePath -> DE.ElfMachine -> DE.ElfClass w -> AmbientException
  -- | The file is a valid PE binary, but for an unsupported architecture
  UnsupportedPEArchitecture :: Maybe FilePath -> AmbientException

deriving instance Show AmbientException
instance X.Exception AmbientException

instance PP.Pretty AmbientException where
  pretty e =
    case e of
      UnsupportedBinaryFormat Nothing ->
        PP.pretty "Unsupported binary format"
      UnsupportedBinaryFormat (Just p) ->
        PP.pretty "Unsupported binary format for file " <> PP.dquotes (PP.pretty p)
      UnsupportedELFArchitecture Nothing m k ->
        PP.hsep [ PP.pretty "Unsupported ELF architecture:"
                , PP.viaShow m <> PP.parens (PP.pretty (DE.elfClassBitWidth k) <> PP.pretty " bit")
                ]
      UnsupportedELFArchitecture (Just p) m k ->
        PP.hsep [ PP.pretty "Unsupported ELF architecture in"
                , PP.dquotes (PP.pretty p) <> PP.pretty ":"
                , PP.viaShow m <> PP.parens (PP.pretty (DE.elfClassBitWidth k) <> PP.pretty " bit")
                ]
      UnsupportedPEArchitecture Nothing ->
        PP.pretty "Unsupported PE file"
      UnsupportedPEArchitecture (Just p) ->
        PP.pretty "Unsupported PE file " <> PP.dquotes (PP.pretty p)
