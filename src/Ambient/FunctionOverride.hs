{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Ambient.FunctionOverride (
    FunctionOverride(..)
  , SomeFunctionOverride(..)
  , FunctionABI(..)
  , BuildFunctionABI(..)
    -- * Overrides
  , buildMallocOverride
  , buildCallocOverride
    -- * Hacky overrides
  , hackyFreeOverride
  , hackyGdErrorExOverride
  , hackyPrintfOverride
  , buildHackyBumpMallocOverride
  , buildHackyBumpCallocOverride
    -- * Crucible syntax
  , ExtensionParser
  , SomeExtensionWrapper(..)
  , extensionParser
  , extensionTypeParser
  , loadCrucibleSyntaxOverrides
  , wrapPointerAdd
  ) where

import           Control.Applicative ( empty )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Control.Monad.State.Class ( MonadState )
import           Control.Monad.Writer.Class ( MonadWriter )
import qualified Data.BitVector.Sized as BVS
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.Nonce as Nonce
import qualified Data.Parameterized.Pair as Pair
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.String as DS
import qualified Data.Text as DT
import qualified Data.Text.IO as DTI
import           GHC.TypeNats ( KnownNat, type (<=) )
import qualified System.FilePath as SF
import qualified System.FilePath.Glob as SFG
import qualified Text.Megaparsec as MP

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.CFG.Expr as LCE
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.CFG.SSAConversion as LCCS
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.Syntax.ExprParse as LCSE
import qualified Lang.Crucible.Syntax.SExpr as LCSS
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP

import           Ambient.Override
import qualified Ambient.Exception as AE
import qualified Ambient.FunctionOverride.ArgumentMapping as AFA

-------------------------------------------------------------------------------
-- Function Call Overrides
-------------------------------------------------------------------------------

-- | FunctionOverride captures an override and type information about how to
-- call it
data FunctionOverride p sym args ext ret =
  FunctionOverride { functionName :: WF.FunctionName
                   -- ^ Name of the function
                   , functionArgTypes :: LCT.CtxRepr args
                   -- ^ Types of the arguments to the function
                   , functionReturnType :: LCT.TypeRepr ret
                   -- ^ Return type of the function
                   , functionOverride
                       :: (LCB.IsSymInterface sym)
                       => sym
                       -> Ctx.Assignment (LCS.RegEntry sym) args
                       -- Arguments to function
                       -> (forall rtp args' ret'. LCS.OverrideSim p sym ext rtp args' ret' (LCS.RegValue sym ret))
                   -- ^ Override capturing behavior of the function
                   }

data SomeFunctionOverride p sym ext =
  forall args ret . SomeFunctionOverride (FunctionOverride p sym args ext ret)

buildCallocOverride :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                                            Ctx.::> LCLM.LLVMPointerType 64) ext
                                              (LCLM.LLVMPointerType 64)
buildCallocOverride mvar = FunctionOverride
  { functionName = "calloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCLM.LLVMPointerRepr LCT.knownNat
  , functionOverride = \sym args -> Ctx.uncurryAssignment (callCalloc sym mvar) args
  }

callCalloc :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
           => sym
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
              -- ^ The number of elements in the array
           -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
callCalloc sym mvar (LCS.regValue -> num) (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let ?ptrWidth = LCT.knownNat @64
     numBV <- LCLM.projectLLVM_bv sym num
     szBV  <- LCLM.projectLLVM_bv sym sz
     LCLM.doCalloc sym mem szBV numBV LCLD.noAlignment

buildMallocOverride :: LCB.IsSymInterface sym
                    => LCS.GlobalVar LCLM.Mem
                    -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64) ext
                                              (LCLM.LLVMPointerType 64)
buildMallocOverride mvar = FunctionOverride
  { functionName = "malloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCLM.LLVMPointerRepr LCT.knownNat
  , functionOverride = \sym args -> Ctx.uncurryAssignment (callMalloc sym mvar) args
  }

callMalloc :: LCB.IsSymInterface sym
           => sym
           -> LCS.GlobalVar LCLM.Mem
           -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
              -- ^ The number of bytes to allocate
           -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
callMalloc sym mvar (LCS.regValue -> sz) =
  LCS.modifyGlobal mvar $ \mem -> liftIO $
  do let ?ptrWidth = LCT.knownNat @64
     let displayString = "<malloc function override>"
     szBV <- LCLM.projectLLVM_bv sym sz
     LCLM.doMalloc sym LCLM.HeapAlloc LCLM.Mutable displayString mem szBV LCLD.noAlignment

-------------------------------------------------------------------------------
-- Hacky Overrides
-------------------------------------------------------------------------------

-- These are crude overrides that are primarily meant as a shortcut to getting
-- something to work. We should replace these with proper solutions later.
-- See #19 for one possible way to do this.

hackyBumpMalloc :: LCB.IsSymInterface sym
                => sym
                -> LCS.GlobalVar (LCLM.LLVMPointerType 64)
                -- ^ Global pointing to end of heap bump allocation
                -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                -- ^ The number of bytes to allocate
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
hackyBumpMalloc sym endGlob (LCS.regValue -> sz) = do
  szBv <- liftIO $ LCLM.projectLLVM_bv sym sz
  LCS.modifyGlobal endGlob $ \endPtr -> liftIO $ do
    -- Bump up end pointer
    endPtr' <- LCLM.ptrSub sym (LCT.knownNat @64) endPtr szBv
    return (endPtr', endPtr')

buildHackyBumpMallocOverride
  :: LCB.IsSymInterface sym
  => LCS.GlobalVar (LCLM.LLVMPointerType 64)
  -- ^ Global pointing to end of heap bump allocation
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64) ext
                                              (LCLM.LLVMPointerType 64)
buildHackyBumpMallocOverride endGlob = FunctionOverride
  { functionName = "malloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCLM.LLVMPointerRepr LCT.knownNat
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyBumpMalloc sym endGlob) args
  }

hackyBumpCalloc :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
                => sym
                -> LCS.GlobalVar (LCLM.LLVMPointerType 64)
                -- ^ Global pointing to end of heap bump allocation
                -> LCS.GlobalVar LCLM.Mem
                -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                -- ^ The number of elements in the array
                -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                -- ^ The number of bytes to allocate
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
hackyBumpCalloc sym endGlob memVar (LCS.regValue -> num) (LCS.regValue -> sz) = do
  let ?ptrWidth = LCT.knownNat @64
  LCS.modifyGlobal endGlob $ \endPtr -> do
    res <- LCS.modifyGlobal memVar $ \mem -> liftIO $ do
      -- Bump up end pointer
      numBV <- LCLM.projectLLVM_bv sym num
      szBV  <- LCLM.projectLLVM_bv sym sz
      allocSzBv <- WI.bvMul sym numBV szBV
      endPtr' <- LCLM.ptrSub sym (LCT.knownNat @64) endPtr allocSzBv

      -- Zero memory
      zero <- WI.bvLit sym WI.knownNat (BVS.zero WI.knownNat)
      mem' <- LCLM.doMemset sym LCT.knownNat mem endPtr' zero allocSzBv
      return (endPtr', mem')
    return (res, res)

buildHackyBumpCallocOverride
  :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
  => LCS.GlobalVar (LCLM.LLVMPointerType 64)
  -> LCS.GlobalVar LCLM.Mem
  -> FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                          Ctx.::> LCLM.LLVMPointerType 64) ext
                            (LCLM.LLVMPointerType 64)
buildHackyBumpCallocOverride endGlob memVar = FunctionOverride
  { functionName = "calloc"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr (LCT.knownNat @64) Ctx.:> LCLM.LLVMPointerRepr (LCT.knownNat @64)
  , functionReturnType = LCLM.LLVMPointerRepr (LCT.knownNat @64)
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyBumpCalloc sym endGlob memVar) args
  }

-- | Mock @free@ by doing nothing.
hackyFreeOverride :: LCB.IsSymInterface sym
                  => FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64) ext
                                            LCT.UnitType
hackyFreeOverride = FunctionOverride
  { functionName = "free"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyCallFree sym) args
  }

hackyCallFree :: LCB.IsSymInterface sym
              => sym
              -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
              -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym LCT.UnitType)
hackyCallFree _sym _ptr = pure ()

-- | Mock @gd_error_ex@ by doing nothing.
hackyGdErrorExOverride :: LCB.IsSymInterface sym
                       => FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                                               Ctx.::> LCLM.LLVMPointerType 64
                                                               Ctx.::> LCLM.LLVMPointerType 64) ext
                                                 LCT.UnitType
hackyGdErrorExOverride = FunctionOverride
  { functionName = "gd_error_ex"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                                 Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                                 Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCT.UnitRepr
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyCallGdErrorEx sym) args
  }

hackyCallGdErrorEx :: LCB.IsSymInterface sym
                   => sym
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                   -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                   -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym LCT.UnitType)
hackyCallGdErrorEx _sym _priority _format _va_args = pure ()

-- | Mock @printf@ by doing nothing and returing zero.
hackyPrintfOverride :: LCB.IsSymInterface sym
                    => FunctionOverride p sym (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType 64
                                                            Ctx.::> LCLM.LLVMPointerType 64) ext
                                              (LCLM.LLVMPointerType 64)
hackyPrintfOverride = FunctionOverride
  { functionName = "printf"
  , functionArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                                 Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , functionReturnType = LCLM.LLVMPointerRepr LCT.knownNat
  , functionOverride = \sym args -> Ctx.uncurryAssignment (hackyCallPrintf sym) args
  }

hackyCallPrintf :: LCB.IsSymInterface sym
                => sym
                -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                -> LCS.RegEntry sym (LCLM.LLVMPointerType 64)
                -> LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCLM.LLVMPointerType 64))
hackyCallPrintf sym _format _va_args = liftIO $ do
  let intRepr = LCT.knownNat @32
  zeroBV <- WI.bvLit sym intRepr $ BVS.zero intRepr
  bvToPtr sym zeroBV

-------------------------------------------------------------------------------
-- Function Call ABI Specification
-------------------------------------------------------------------------------

-- Now we actually need to perform the architecture-specific mapping. We can
-- use the type-level information in the override signatures to help us (and
-- especially the type repr inside of the FunctionCall type)
--
-- Note that this is data rather than a class because there can be different
-- ABIs for a given architecture (e.g., Windows and Linux)
data FunctionABI arch sym p =
  FunctionABI {
    -- Given a full register state, extract all of the arguments we need for
    -- the function call
    functionIntegerArgumentRegisters
      :: forall atps
       . LCT.CtxRepr atps
      -- Types of argument registers
      -> Ctx.Assignment (LCS.RegValue' sym) (DMS.MacawCrucibleRegTypes arch)
      -- Argument register values
      -> Ctx.Assignment (LCS.RegEntry sym) atps
      -- Function argument values

    -- Build an OverrideSim action with appropriate return register types from
    -- a given OverrideSim action
  , functionIntegerReturnRegisters
     :: forall t r args rtp
      . LCT.TypeRepr t
     -- Function return type
     -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym t)
     -- OverrideSim action producing the functions's return value
     -> LCS.RegValue sym (DMS.ArchRegStruct arch)
     -- Argument register values from before function execution
     -> LCS.OverrideSim p sym (DMS.MacawExt arch) r args rtp (LCS.RegValue sym (DMS.ArchRegStruct arch))
     -- OverrideSim action with return type matching system return register
     -- type

    -- A mapping from function names to overrides
  , functionNameMapping
     :: (LCB.IsSymInterface sym, LCLM.HasLLVMAnn sym)
     => Map.Map WF.FunctionName (SomeFunctionOverride p sym (DMS.MacawExt arch))
  }

-- A function to construct a FunctionABI with memory access
newtype BuildFunctionABI arch sym p = BuildFunctionABI (
       LCB.IsSymInterface sym
    => LCS.GlobalVar (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
    -> LCS.GlobalVar LCLM.Mem
    -- MemVar for the execution
    -> [ SomeFunctionOverride p sym (DMS.MacawExt arch) ]
    -- Additional overrides
    -> FunctionABI arch sym p
  )

-------------------------------------------------------------------------------
-- Crucible Syntax
-------------------------------------------------------------------------------

-- This section contains all of the infrastructure for supporting crucible
-- syntax overrides.

-- | Load all crucible syntax function overrides in an override directory.
-- This function reads all files matching @<dirPath>/function/*.cbl@ and
-- generates FunctionOverrides for them.
loadCrucibleSyntaxOverrides :: LCCE.IsSyntaxExtension ext
                            => FilePath
                            -- ^ Override directory
                            -> Nonce.NonceGenerator IO s
                            -> LCF.HandleAllocator
                            -> LCSC.ParserHooks ext
                            -- ^ ParserHooks for the desired syntax xtension
                            -> IO [SomeFunctionOverride p sym ext]
                            -- ^ A list of loaded overrides
loadCrucibleSyntaxOverrides dirPath ng halloc hooks = do
  paths <- SFG.namesMatching (dirPath SF.</> "function" SF.</> "*.cbl")
  mapM go paths
  where
    go path = do
      acfg <- loadCrucibleSyntaxOverride path
      let name = DS.fromString (SF.takeBaseName path)
      return (acfgToFunctionOverride name acfg)

    -- Load a single crucible syntax override
    loadCrucibleSyntaxOverride path = do
      contents <- DTI.readFile path
      let parsed = MP.parse (  LCSS.skipWhitespace
                            *> MP.many (LCSS.sexp LCSA.atom)
                            <* MP.eof)
                            path
                            contents
      case parsed of
        Left err ->
          CMC.throwM (AE.CrucibleSyntaxFailure (MP.errorBundlePretty err))
        Right asts -> do
          let ?parserHooks = hooks
          eAcfgs <- LCSC.top ng halloc [] $ LCSC.cfgs asts
          case eAcfgs of
            Left err -> CMC.throwM (AE.CrucibleSyntaxFailure (show err))
            Right acfgs -> case List.find (isOverride path) acfgs of
              Nothing -> CMC.throwM (AE.CrucibleSyntaxFailure (
                   "Expected to find a function named '"
                ++ (SF.takeBaseName path)
                ++ "' in '"
                ++ path
                ++ "'"))
              Just acfg -> return acfg

-- Convert an ACFG to a FunctionOverride
acfgToFunctionOverride
  :: WF.FunctionName
  -> LCSC.ACFG ext
  -> SomeFunctionOverride p sym ext
acfgToFunctionOverride name (LCSC.ACFG argTypes retType cfg) =
  let argMap = AFA.bitvectorArgumentMapping argTypes
      (ptrTypes, ptrTypeMapping) = AFA.pointerArgumentMappping argMap
      retRepr = AFA.promoteBVToPtr retType
  in case LCCS.toSSA cfg of
       LCCC.SomeCFG ssaCfg ->
         SomeFunctionOverride $ FunctionOverride
         { functionName = name
         , functionArgTypes = ptrTypes
         , functionReturnType = retRepr
         , functionOverride = \sym args -> do
             -- Translate any arguments that are LLVMPointers but should be Bitvectors into Bitvectors
             --
             -- This generates side conditions asserting that the block ID is zero
             pointerArgs <- liftIO $ AFA.buildFunctionOverrideArgs sym argMap ptrTypeMapping args
             userRes <- LCS.callCFG ssaCfg (LCS.RegMap pointerArgs)
             -- Convert any BV returns from the user override to LLVMPointers
             LCS.regValue <$> liftIO (AFA.convertBitvector sym retRepr userRes)
         }

isOverride :: String -> LCSC.ACFG ext -> Bool
isOverride path (LCSC.ACFG _ _ g) =
  LCF.handleName (LCCR.cfgHandle g) == DS.fromString (SF.takeBaseName path)

-- | Parser for type extensions to crucible syntax
extensionTypeParser
  :: (LCSE.MonadSyntax LCSA.Atomic m, 1 <= w)
  => PN.NatRepr w
  -> m (Some LCT.TypeRepr)
extensionTypeParser ptrWidth = do
  LCSA.AtomName name <- LCSC.atomName
  case DT.unpack name of
    "Pointer" -> return $ Some (LCLM.LLVMPointerRepr ptrWidth)
    _ -> empty

-- | The constraints on the abstract parser monad
type ExtensionParser m ext s = ( LCSE.MonadSyntax LCSA.Atomic m
                               , MonadWriter [WP.Posd (LCCR.Stmt ext s)] m
                               , MonadState (LCSC.SyntaxState s) m
                               , MonadIO m
                               , LCCE.IsSyntaxExtension ext
                               )

-- | Parser for syntax extensions to crucible syntax
--
-- Note that the return value is a 'Pair.Pair', which seems a bit strange
-- because the 'LCT.TypeRepr' in the first of the pair is redundant (it can be
-- recovered by inspecting the 'LCCR.Atom'). The return value is set up this way
-- because the use site of the parser in crucible-syntax expects the 'Pair.Pair'
-- for all of the parsers that it attempts; returning the 'Pair.Pair' here
-- simplifies the use site.
extensionParser :: forall s m ext arch
                 . ( ExtensionParser m ext s
                   , ext ~ (DMS.MacawExt arch)
                   )
                => Map.Map LCSA.AtomName (SomeExtensionWrapper arch)
                -- ^ Mapping from names to syntax extensions
                -> LCSC.ParserHooks ext
                -- ^ ParserHooks for the desired syntax extension
                -> m (Pair.Pair LCT.TypeRepr (LCCR.Atom s))
                -- ^ A pair containing a result type and an atom of that type
extensionParser extensionWrappers hooks =
  LCSE.depCons LCSC.atomName $ \name ->
    case Map.lookup name extensionWrappers of
      Nothing -> empty
      Just (SomeExtensionWrapper w) -> do
        loc <- LCSE.position
        let ?parserHooks = hooks
        -- Generate atoms for the arguments to this extension
        operandAtoms <- LCSC.operands (extArgTypes w)
        -- Pass these atoms to the extension wrapper and return an atom for the
        -- resulting value
        atomVal <- extWrapper w operandAtoms
        let retType = LCCR.typeOfAtomValue atomVal
        endAtom <- LCSC.freshAtom loc atomVal
        return (Pair.Pair retType endAtom)

-- | A wrapper for a syntax extension statement
--
-- Note that these are pure and are intended to guide the substitution of syntax
-- extensions for operations in the 'MDS.MacawExt' syntax.
data ExtensionWrapper arch args ret =
  ExtensionWrapper { extName :: LCSA.AtomName
                  -- ^ Name of the syntax extension
                   , extArgTypes :: LCT.CtxRepr args
                  -- ^ Types of the arguments to the syntax extension
                   , extRetType :: LCT.TypeRepr ret
                  -- ^ Return type of the syntax extension
                   , extWrapper :: forall s m
                                 . ( ExtensionParser m (DMS.MacawExt arch) s)
                                => Ctx.Assignment (LCCR.Atom s) args
                                -> m (LCCR.AtomValue (DMS.MacawExt arch) s ret)
                  -- ^ Syntax extension wrapper that takes the arguments passed
                  -- to the extension operator, returning a suitable crucible
                  -- 'LCCR.AtomValue' to represent it in the syntax extension.
                   }

data SomeExtensionWrapper arch =
  forall args ret. SomeExtensionWrapper (ExtensionWrapper arch args ret)

-- | Wrapper for the 'DMS.PtrAdd' syntax extension that enables users to add
-- integer offsets to pointers:
--
-- > pointer-add ptr offset
--
-- Note that the underlying macaw primitive allows the offset to be in either
-- position. This user-facing interface is more restrictive.
wrapPointerAdd
  :: ( 1 <= w
     , KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCT.BVType w)
                      (LCLM.LLVMPointerType w)
wrapPointerAdd = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-add"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> LCT.BVRepr LCT.knownNat
  , extRetType = WI.knownRepr
  , extWrapper = \args -> Ctx.uncurryAssignment pointerAdd args }

-- | Add an integer offset to a pointer using 'DMS.PtrAdd'
--
-- Note: we could make this more general to accept any width bitvector offset
pointerAdd :: forall arch w m s tp ext
            . ( w ~ DMC.ArchAddrWidth arch
              , 1 <= w
              , KnownNat w
              , DMC.MemWidth w
              , tp ~ LCLM.LLVMPointerType w
              , ext ~ DMS.MacawExt arch
              , ExtensionParser m ext s
              )
           => LCCR.Atom s (LCLM.LLVMPointerType w)
           -- ^ LHS of pointer addition (the pointer)
           -> LCCR.Atom s (LCT.BVType w)
           -- ^ RHS of pointer addition (the offset)
           -> m (LCCR.AtomValue (DMS.MacawExt arch) s tp)
pointerAdd p1 p2 = do
  toPtrAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr WI.knownNat p2)))
  let addExt = DMS.PtrAdd (DMC.addrWidthRepr WI.knownNat) p1 toPtrAtom
  return (LCCR.EvalExt addExt)
