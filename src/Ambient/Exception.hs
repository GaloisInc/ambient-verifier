{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Ambient.Exception (
  AmbientException(..)
  ) where

import qualified Control.Exception as X
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit as DE
import qualified Data.Text as T
import qualified Prettyprinter as PP
import qualified Text.Megaparsec as MP

import qualified Data.Macaw.Memory as DMM
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.Syntax.ExprParse as LCSE
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF

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
  -- | A symbolic function address could not be resolved as concrete
  SymbolicFunctionAddress :: AmbientException
  -- | The solver returned @UNKNOWN@ when trying to resolve a function address
  SolverUnknownFunctionAddress :: AmbientException
  -- | Symbolic execution timed out, and no result is available
  ExecutionTimeout :: AmbientException
  -- | The event trace for the named property is malformed
  MalformedEventTrace :: T.Text -> AmbientException
  -- | A failure from Megaparsec in a crucible syntax override
  CrucibleSyntaxMegaparsecFailure :: (MP.VisualStream s, MP.TraversableStream s, MP.ShowErrorComponent e, Show s, Show (MP.Token s), Show e) => MP.ParseErrorBundle s e -> AmbientException
  -- | A failure during expression parsing in a crucible syntax override
  CrucibleSyntaxExprParseFailure :: LCSC.ExprErr s -> AmbientException
  -- | Could not find a function in a crucible syntax file
  CrucibleSyntaxFunctionNotFound :: String -> FilePath -> AmbientException
  -- | Global variable declared with an unsuported type
  UnsuportedGlobalVariableType :: String -> LCT.TypeRepr t -> AmbientException
  -- | Crucible syntax test function has an illegal type signature
  IllegalCrucibleSyntaxTestSignature :: FilePath -> WF.FunctionName -> AmbientException
  -- | Binary contains functions in multiple memory regions
  MultipleFunctionRegions :: AmbientException

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
      SymbolicFunctionAddress ->
        PP.pretty "Attempted to call function with non-concrete address"
      SolverUnknownFunctionAddress ->
        PP.pretty "Solving function address yielded UNKNOWN"
      UnsupportedSyscallNumber syscallNum ->
        PP.pretty "Failed to find override for syscall:" PP.<+> PP.viaShow syscallNum
      ExecutionTimeout ->
        PP.pretty "Symbolic execution timed out"
      MalformedEventTrace name ->
        PP.pretty "The event trace for property'" <> PP.pretty name <> PP.pretty "' is malformed"
      CrucibleSyntaxMegaparsecFailure err ->
        PP.pretty "Parse failure in crucible syntax override: " <> PP.pretty (MP.errorBundlePretty err)
      CrucibleSyntaxExprParseFailure err ->
        PP.pretty "Parse failure in crucible syntax override: " <>
          case err of
            LCSC.SyntaxParseError se -> PP.pretty (LCSE.printSyntaxError se)
            _ -> PP.pretty (show err)
      CrucibleSyntaxFunctionNotFound name path ->
        PP.pretty "Expected to find a function named '" <> PP.pretty name <> PP.pretty "' in '" <> PP.pretty path <> PP.pretty "'"
      UnsuportedGlobalVariableType name tp ->
        PP.pretty "Unable to construct symbolic value for global variable '" <> PP.pretty name <> PP.pretty "' with type '" <> PP.pretty tp <> PP.pretty "'"
      IllegalCrucibleSyntaxTestSignature path fnName ->
        PP.pretty "Test function '" <> PP.pretty fnName <> PP.pretty "' in file '" <> PP.pretty path <> PP.pretty "' has an illegal type signature.  Test functions must take no arguments and have a 'Unit' return type."
      MultipleFunctionRegions ->
        PP.pretty "Binaries containing functions in multiple memory regions are not currently supported."
