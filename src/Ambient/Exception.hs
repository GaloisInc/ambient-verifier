{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Ambient.Exception (
  AmbientException(..)
  ) where

import qualified Control.Exception as X
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit as DE
import qualified Prettyprinter as PP

import qualified Data.Macaw.Memory as DMM

data AmbientException where
  -- | The given binary format is not supported
  --
  -- We don't necessarily know what it is, and we may not have a filename (if
  -- the verifier was just passed a bytestring with no filename)
  UnsupportedBinaryFormat :: FilePath -> AmbientException
  -- | The file was a valid ELF binary, but for an architecture that we do not support
  UnsupportedELFArchitecture :: FilePath -> DE.ElfMachine -> DE.ElfClass w -> AmbientException
  -- | The file is a valid PE binary, but for an unsupported architecture
  UnsupportedPEArchitecture :: FilePath -> AmbientException
  -- | The executable was missing an expected symbol
  MissingExpectedSymbol :: BSC.ByteString -> AmbientException
  -- | There was not function discovered at the given address (with an optional name)
  MissingExpectedFunction :: (DMM.MemWidth w) => Maybe BSC.ByteString -> DMM.MemSegmentOff w -> AmbientException
  -- | The requested solver and float mode representation is not supported
  UnsupportedSolverCombination :: String -> String -> AmbientException
  -- | A symbolic syscall number could not be resolved as concrete
  SymbolicSyscallNumber :: AmbientException
  -- | The solver returned @UNKNOWN@ when trying to resolve a syscall number
  SolverUnknownSyscallNumber :: AmbientException
  -- | There is no model for this syscall number
  UnsupportedSyscallNumber :: Integer -> AmbientException

deriving instance Show AmbientException
instance X.Exception AmbientException

instance PP.Pretty AmbientException where
  pretty e =
    case e of
      UnsupportedBinaryFormat p ->
        PP.pretty "Unsupported binary format for file " <> PP.dquotes (PP.pretty p)
      UnsupportedELFArchitecture p m k ->
        PP.hsep [ PP.pretty "Unsupported ELF architecture in"
                , PP.dquotes (PP.pretty p) <> PP.pretty ":"
                , PP.viaShow m <> PP.parens (PP.pretty (DE.elfClassBitWidth k) <> PP.pretty " bit")
                ]
      UnsupportedPEArchitecture p ->
        PP.pretty "Unsupported PE file " <> PP.dquotes (PP.pretty p)
      MissingExpectedSymbol sym ->
        PP.pretty "Missing expected symbol: " <> PP.pretty (BSC.unpack sym)
      MissingExpectedFunction Nothing addr ->
        PP.pretty "A function was expected, but not discovered, at address " <> PP.pretty addr
      MissingExpectedFunction (Just fname) addr ->
        PP.pretty "Function " <> PP.pretty (BSC.unpack fname) <> PP.pretty " was expected, but not found, at address " <> PP.pretty addr
      UnsupportedSolverCombination solver fm ->
        PP.pretty "The " <> PP.pretty solver <> PP.pretty " SMT solver does not support the " <> PP.pretty fm <> PP.pretty " floating point mode"
      SymbolicSyscallNumber ->
        PP.pretty "Attempted to make system call with non-concrete syscall number"
      SolverUnknownSyscallNumber ->
        PP.pretty "Solving syscall number yielded UNKNOWN"
      UnsupportedSyscallNumber syscallNum ->
        PP.pretty "Failed to find override for syscall:" PP.<+> PP.viaShow syscallNum
