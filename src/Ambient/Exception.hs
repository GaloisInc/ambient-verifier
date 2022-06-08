{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Ambient.Exception (
    AmbientException(..)
  , ConcretizationTarget(..)
  , NetworkFunctionArgument(..)
  ) where

import qualified Control.Exception as X
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit as DE
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Text as T
import qualified Prettyprinter as PP
import qualified Text.Megaparsec as MP

import qualified Data.Macaw.Memory as DMM
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.Syntax.ExprParse as LCSE
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF
import qualified What4.ProgramLoc as WP

import qualified Ambient.Loader.Versioning as ALV

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
  -- | A symbolic value could not be resolved as concrete
  ConcretizationFailedSymbolic :: WP.ProgramLoc -> ConcretizationTarget -> AmbientException
  -- | The solver returned @UNKNOWN@ when trying to resolve a value as concrete
  ConcretizationFailedUnknown :: WP.ProgramLoc -> ConcretizationTarget -> AmbientException
  -- | There is no model for this syscall number
  UnsupportedSyscallNumber :: Integer -> AmbientException
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
  CrucibleSyntaxFunctionNotFound :: WF.FunctionName -> FilePath -> AmbientException
  -- | The provided crucible syntax directory doesn't exist
  CrucibleOverrideDirectoryNotFound :: FilePath -> AmbientException
  -- | A @<name>.cbl@ file defines more than one function named @<name@>.
  DuplicateNamesInCrucibleOverride :: FilePath -> WF.FunctionName -> AmbientException
  -- | Global variable declared with an unsupported type
  UnsuportedGlobalVariableType :: String -> LCT.TypeRepr t -> AmbientException
  -- | Crucible syntax test function has an illegal type signature
  IllegalCrucibleSyntaxTestSignature :: FilePath -> WF.FunctionName -> AmbientException
  -- | Binary contains functions in multiple memory regions
  MultipleFunctionRegions :: AmbientException
  -- | aarch32 binary contains an unsupported .plt.got section
  Aarch32BinaryHasPltGot :: AmbientException
  -- | Encountered a PLT stub without an accompanying override or
  -- implementation
  UnhandledPLTStub :: ALV.VersionedFunctionName -> AmbientException
  -- | The @socket@ function was invoked with an unsupported argument.
  -- See @Note [The networking story]@ in "Ambient.Syscall.Overrides".
  UnsupportedSocketArgument :: NetworkFunctionArgument -> Integer -> AmbientException
  -- | A provided shared object had a different ELF machine value than the main
  -- binary.  The first argument is the 'DE.ElfMachine' for the shared object
  -- and the second argument is the 'DE.ElfMachine' for the main binary.
  SoMismatchedElfMachine :: DE.ElfMachine -> DE.ElfMachine -> AmbientException
  -- | A provided shared object had a different ELF class value than the main
  -- binary.  The first argument is the 'DE.ElfClass' for the shared object
  -- and the second argument is the 'DE.ElfClass' for the main binary.
  SoMismatchedElfClass :: DE.ElfClass w -> DE.ElfClass w' -> AmbientException
  -- | The offset for the entry point function's address could not be resolved.
  EntryPointAddrOffResolutionFailure :: DMM.MemWidth w => DMM.MemWord w -> AmbientException
  -- | An address corresponding to the name of the entry point function could not be found.
  NamedEntryPointAddrLookupFailure :: WF.FunctionName -> AmbientException
  -- | An aarch32 binary contains a .rela.dyn section
  Aarch32RelaDynUnsupported :: AmbientException
  -- | Simulation encountered a read from an unsupported relocation type.  The
  -- argument is the name of the relocation type.
  UnsupportedRelocation :: String -> AmbientException
  -- | Encountered an error when parsing a dynamic section in an ELF binary.
  ElfDynamicParseError :: FilePath -> DE.DynamicError -> AmbientException
  -- | Could not constuct a virtual address map for an ELF binary.
  ElfVirtualAddressMapError :: FilePath -> AmbientException
  -- | Encountered an error when parsing the @DT_NEEDED@ entries in a dynamic ELF binary.

  -- Unfortunately, elf-edit's @dynNeeded@ function only returns a String when
  -- it errors, so that is as precise as we can make things without changing
  -- the upstream elf-edit API.
  ElfDynamicNeededError :: FilePath -> String -> AmbientException
  -- | Encountered multiple @PT_DYNAMIC@ program headers when parsing an ELF
  -- binary.
  ElfMultipleDynamicHeaders :: FilePath -> AmbientException
  -- | Encountered a shared library that is not dynamically linked.
  ElfNonDynamicSharedLib :: FilePath -> AmbientException
  -- | Tried to retrieve a shared memory segment with a symbolic ID
  SymbolicSharedMemorySegmentId :: AmbientException
  -- | The @function address overrides@ section of an @overrides.yaml@ file
  -- contained a function name without a corresponding @.cbl@ file.
  FunctionAddressOverridesNameNotFound ::
    DMM.MemWidth w => FilePath -> DMM.MemWord w -> WF.FunctionName -> AmbientException
  -- | When resolving a forward declaration, a function with the same name
  -- could not be found.
  ForwardDeclarationNameNotFound :: WF.FunctionName -> AmbientException
  -- | When resolving a forward declaration, the function to resolve to has a
  -- different number of arguments than stated in the declaration.
  ForwardDeclarationArgumentNumberMismatch ::
    WF.FunctionName -> LCT.CtxRepr fwdDecArgTys -> LCT.CtxRepr resolvedFnArgTys -> AmbientException
  -- | Unable to narrow a type down from a specific bitvector length when invoking a function.
  FunctionTypeBvNarrowingError :: LCT.NatRepr w -> AmbientException
  -- | Unable to zero-extend a type to a specific bitvector length when invoking a function.
  FunctionTypeBvExtensionError :: LCT.NatRepr w -> AmbientException
  -- | Unable to convert from one type to another when invoking a function.
  -- This is about as vague as error messages get, so if possible, use one of
  -- the @FunctionTypeBv-@ error messages above instead.
  FunctionTypeMismatch :: AmbientException

deriving instance Show AmbientException
instance X.Exception AmbientException

-- | What sort of value did a solver try to resolve as concrete?
data ConcretizationTarget
  = FunctionAddress
  | SyscallNumber
  | NetworkFunction
      T.Text -- The function being invoked
      NetworkFunctionArgument -- The argument to the function for which
                              -- concretization was attempted
  deriving Show

-- | Which argument to a networking-related override did a solver try to
-- resolve as concrete?
data NetworkFunctionArgument
  = FDArgument
  | DomainArgument
  | TypeArgument
  | PortArgument
  deriving Show

concretizationTargetDescription :: ConcretizationTarget -> PP.Doc a
concretizationTargetDescription FunctionAddress = PP.pretty "function address"
concretizationTargetDescription SyscallNumber   = PP.pretty "syscall number"
concretizationTargetDescription (NetworkFunction _ arg) =
  networkFunctionArgumentDescription arg

concretizationTargetCall :: ConcretizationTarget -> PP.Doc a
concretizationTargetCall FunctionAddress = PP.pretty "function call"
concretizationTargetCall SyscallNumber   = PP.pretty "system call"
concretizationTargetCall (NetworkFunction nm _) =
  PP.pretty "a call to the " PP.<+> PP.squotes (PP.pretty nm) PP.<+> PP.pretty "function"

networkFunctionArgumentDescription :: NetworkFunctionArgument -> PP.Doc a
networkFunctionArgumentDescription FDArgument     = PP.pretty "file descriptor argument"
networkFunctionArgumentDescription DomainArgument = PP.pretty "domain argument"
networkFunctionArgumentDescription TypeArgument   = PP.pretty "type argument"
networkFunctionArgumentDescription PortArgument   = PP.pretty "port argument"

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
      ConcretizationFailedSymbolic loc target ->
        PP.pretty "Attempted to make" PP.<+> concretizationTargetCall target PP.<+>
        PP.pretty "with non-concrete" PP.<+> concretizationTargetDescription target PP.<+> PP.pretty "at" PP.<+>
        PP.pretty (WP.plSourceLoc loc)
      ConcretizationFailedUnknown loc target ->
        PP.pretty "Solving" PP.<+> concretizationTargetDescription target PP.<+>
        PP.pretty "yielded UNKNOWN at" PP.<+> PP.pretty (WP.plSourceLoc loc)
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
      DuplicateNamesInCrucibleOverride path fnName ->
        PP.pretty "Override" PP.<+> PP.squotes (PP.pretty path) PP.<+>
        PP.pretty "contains multiple" PP.<+> PP.squotes (PP.pretty fnName) PP.<+>
        PP.pretty "functions"
      CrucibleOverrideDirectoryNotFound path ->
        PP.pretty "Crucible syntax override directory not found: " <> PP.pretty path
      UnsuportedGlobalVariableType name tp ->
        PP.pretty "Unable to construct symbolic value for global variable '" <> PP.pretty name <> PP.pretty "' with type '" <> PP.pretty tp <> PP.pretty "'"
      IllegalCrucibleSyntaxTestSignature path fnName ->
        PP.pretty "Test function '" <> PP.pretty fnName <> PP.pretty "' in file '" <> PP.pretty path <> PP.pretty "' has an illegal type signature.  Test functions must take no arguments and have a 'Unit' return type."
      MultipleFunctionRegions ->
        PP.pretty "Binaries containing functions in multiple memory regions are not currently supported."
      Aarch32BinaryHasPltGot ->
        PP.pretty "aarch32 binaries containing shared library stubs in .plt.got sections are not currently supported."
      UnhandledPLTStub fnName ->
        PP.pretty "Missing implementation or override for shared library function: " <> PP.pretty fnName
      UnsupportedSocketArgument arg value ->
        PP.pretty "Attempted to call the 'socket' function with an unsupported" PP.<+>
        networkFunctionArgumentDescription arg <> PP.colon PP.<+> PP.viaShow value
      SoMismatchedElfMachine soMachine mainMachine ->
        PP.pretty "A shared object has a different ELF machine value than the main binary.  Shared object has machine " PP.<+> PP.viaShow soMachine <> PP.pretty " and main binary has machine " PP.<+> PP.viaShow mainMachine
      SoMismatchedElfClass soClass mainClass ->
        PP.pretty "A shared object has a different ELF class value than the main binary.  Shared object has class " PP.<+> PP.viaShow soClass <> PP.pretty " and main binary has class " PP.<+> PP.viaShow mainClass
      EntryPointAddrOffResolutionFailure addr ->
        PP.pretty "Could not resolve offset for entry point address" PP.<+> PP.pretty addr
      NamedEntryPointAddrLookupFailure fnName ->
        PP.vcat [ PP.pretty "Could not find an address for an entry point function named"
                    PP.<+> PP.squotes (PP.pretty fnName)
                , PP.pretty "Note that if you are verifying a stripped binary,"
                , PP.pretty "you will likely need to supply the address of the entry point"
                , PP.pretty "function using `--entry-point-addr 0xNNN` instead."
                ]
      Aarch32RelaDynUnsupported ->
        PP.pretty "AArch32 binaries containing .rela.dyn sections are not currently supported"
      UnsupportedRelocation relTypeName ->
        PP.pretty "Simulation encountered a read from an unsupported relocation type: " <> PP.pretty relTypeName
      ElfDynamicParseError fp dynErr ->
        PP.vcat [ PP.viaShow dynErr
                , PP.pretty "In the file:" PP.<+> PP.pretty fp
                ]
      ElfVirtualAddressMapError fp ->
        PP.vcat [ PP.pretty "Could not construct virtual address map"
                , PP.pretty "In the file:" PP.<+> PP.pretty fp
                ]
      ElfDynamicNeededError fp errMsg ->
        PP.vcat [ PP.pretty errMsg
                , PP.pretty "In the file:" PP.<+> PP.pretty fp
                ]
      ElfMultipleDynamicHeaders fp ->
        PP.vcat [ PP.pretty"Encountered multiple PT_DYNAMIC program headers"
                , PP.pretty "In the file:" PP.<+> PP.pretty fp
                ]
      ElfNonDynamicSharedLib fp ->
        PP.pretty "The shared library" PP.<+> PP.pretty fp PP.<+> PP.pretty "is not dynamically linked"
      SymbolicSharedMemorySegmentId ->
        PP.pretty "Attempted to retrieve a shared memory segment using a symbolic ID."
      FunctionAddressOverridesNameNotFound binPath addr name ->
        PP.vcat [ PP.pretty "An 'overrides.yaml' file contains a 'function address overrides'"
                , PP.pretty "section with a name that does not correspond to a '*.cbl' file."
                , PP.pretty "- Binary:" PP.<+> PP.pretty binPath
                , PP.pretty "- Address:" PP.<+> PP.pretty addr
                , PP.pretty "- Name:" PP.<+> PP.pretty name
                ]
      ForwardDeclarationNameNotFound fwdDecName ->
        PP.pretty "Could not find a function to resolve the forward declaration named" PP.<+>
        PP.squotes (PP.pretty fwdDecName)
      ForwardDeclarationArgumentNumberMismatch fwdDecName fwdDecArgTys resolvedFnArgTys ->
        PP.vcat [ PP.pretty "The forward declaration for" PP.<+> PP.squotes (PP.pretty fwdDecName) PP.<+>
                  PP.pretty "has" PP.<+> PP.pretty (Ctx.sizeInt (Ctx.size fwdDecArgTys)) PP.<+>
                  PP.pretty "arguments, but"
                , PP.pretty "the resolved function has" PP.<+>
                  PP.pretty (Ctx.sizeInt (Ctx.size resolvedFnArgTys)) PP.<+> PP.pretty "arguments"
                ]
      -- These error messages would be improved if the Pretty instance for
      -- TypeRepr were more human-readable.
      FunctionTypeBvNarrowingError bvLen ->
        PP.vcat [ PP.pretty "Could not narrow a type from a length-" <> PP.viaShow bvLen PP.<+>
                  PP.pretty "bitvector"
                , PP.pretty "when invoking a function"
                ]
      FunctionTypeBvExtensionError bvLen ->
        PP.vcat [ PP.pretty "Could not zero-extend a type to a length-" <> PP.viaShow bvLen PP.<+>
                  PP.pretty "bitvector"
                , PP.pretty "when invoking a function"
                ]
      FunctionTypeMismatch ->
        PP.pretty "Type mismatch when invoking a function"
