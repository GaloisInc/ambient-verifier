{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Ambient.FunctionOverride.Extension (
    TypeAlias(..)
  , TypeLookup(..)
  , ExtensionParser
  , SomeExtensionWrapper(..)
  , extensionParser
  , extensionTypeParser
  , loadCrucibleSyntaxOverrides
  , machineCodeParserHooks
  ) where

import           Control.Applicative ( empty )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Control.Monad.State.Class ( MonadState )
import           Control.Monad.Writer.Class ( MonadWriter )
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
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.CFG.Expr as LCE
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.CFG.SSAConversion as LCCS
import qualified Lang.Crucible.FunctionHandle as LCF
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

import qualified Ambient.Exception as AE
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.ArgumentMapping as AFA

-- | The additional types ambient-verifier supports beyond those built into
-- crucible-syntax.
data TypeAlias = Byte | Int | Long | PidT | Pointer | SizeT | UidT
  deriving (Show, Eq, Enum, Bounded)

-- | A list of every type alias.
allTypeAliases :: [TypeAlias]
allTypeAliases = [minBound .. maxBound]

-- | Lookup function from a 'TypeAlias' to the underlying crucible type it
-- represents.
newtype TypeLookup = TypeLookup (TypeAlias -> (Some LCT.TypeRepr))

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
                            -> IO [AF.SomeFunctionOverride p sym ext]
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
        Left err -> CMC.throwM (AE.CrucibleSyntaxMegaparsecFailure err)
        Right asts -> do
          let ?parserHooks = hooks
          eAcfgs <- LCSC.top ng halloc [] $ LCSC.cfgs asts
          case eAcfgs of
            Left err -> CMC.throwM (AE.CrucibleSyntaxExprParseFailure err)
            Right acfgs -> case List.find (isOverride path) acfgs of
              Nothing ->
                CMC.throwM (AE.CrucibleSyntaxFunctionNotFound (SF.takeBaseName path) path)
              Just acfg -> return acfg

-- Convert an ACFG to a FunctionOverride
acfgToFunctionOverride
  :: WF.FunctionName
  -> LCSC.ACFG ext
  -> AF.SomeFunctionOverride p sym ext
acfgToFunctionOverride name (LCSC.ACFG argTypes retType cfg) =
  let argMap = AFA.bitvectorArgumentMapping argTypes
      (ptrTypes, ptrTypeMapping) = AFA.pointerArgumentMappping argMap
      retRepr = AFA.promoteBVToPtr retType
  in case LCCS.toSSA cfg of
       LCCC.SomeCFG ssaCfg ->
         AF.SomeFunctionOverride $ AF.FunctionOverride
         { AF.functionName = name
         , AF.functionArgTypes = ptrTypes
         , AF.functionReturnType = retRepr
         , AF.functionOverride = \sym args -> do
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
  :: (LCSE.MonadSyntax LCSA.Atomic m)
  => Map.Map LCSA.AtomName (Some LCT.TypeRepr)
  -- ^ A mapping from additional type names to the crucible types they
  -- represent
  -> m (Some LCT.TypeRepr)
extensionTypeParser types = do
  name <- LCSC.atomName
  case Map.lookup name types of
    Just someTypeRepr -> return someTypeRepr
    Nothing -> empty

-- | The constraints on the abstract parser monad
type ExtensionParser m ext s = ( LCSE.MonadSyntax LCSA.Atomic m
                               , MonadWriter [WP.Posd (LCCR.Stmt ext s)] m
                               , MonadState (LCSC.SyntaxState s) m
                               , MonadIO m
                               , LCCE.IsSyntaxExtension ext
                               )

-- | Convert a NatRepr containing a value in bytes to one containing a value in
-- bits.
bytesToBits :: WI.NatRepr m -> WI.NatRepr (8 WI.* m)
bytesToBits = PN.natMultiply (WI.knownNat @8)

-- | Parser for syntax extensions to crucible syntax
--
-- Note that the return value is a 'Pair.Pair', which seems a bit strange
-- because the 'LCT.TypeRepr' in the first of the pair is redundant (it can be
-- recovered by inspecting the 'LCCR.Atom'). The return value is set up this way
-- because the use site of the parser in crucible-syntax expects the 'Pair.Pair'
-- for all of the parsers that it attempts; returning the 'Pair.Pair' here
-- simplifies the use site.
extensionParser :: forall s m ext arch w
                 . ( ExtensionParser m ext s
                   , ext ~ (DMS.MacawExt arch)
                   , w ~ DMC.ArchAddrWidth arch
                   , 1 <= w
                   , KnownNat w
                   , DMM.MemWidth w
                   )
                => Map.Map LCSA.AtomName (SomeExtensionWrapper arch)
                -- ^ Mapping from names to syntax extensions
                -> LCSC.ParserHooks ext
                -- ^ ParserHooks for the desired syntax extension
                -> m (Pair.Pair LCT.TypeRepr (LCCR.Atom s))
                -- ^ A pair containing a result type and an atom of that type
extensionParser wrappers hooks =
  LCSE.depCons LCSC.atomName $ \name ->
    case name of
      LCSA.AtomName "pointer-read" -> do
        -- Pointer reads are a special case because we must parse the number of
        -- bytes to read as well as the endianness of the read before parsing
        -- the additional arguments as Atoms.
        LCSE.depCons LCSC.nat $ \bytes ->
          LCSE.depCons LCSC.atomName $ \endiannessName ->
            case endiannessFromAtomName endiannessName of
              Just endianness ->
                case PN.mkNatRepr bytes of
                  Some bytesRepr | Just PN.LeqProof <- PN.isPosNat bytesRepr
                                 , Just PN.LeqProof <-
                                     PN.isPosNat (bytesToBits bytesRepr) -> do
                    let readWrapper = buildPointerReadWrapper bytesRepr
                                                              endianness
                    go (SomeExtensionWrapper readWrapper)
                  _ -> empty
              Nothing -> empty
      LCSA.AtomName "pointer-write" -> do
        -- Pointer writes are a special case because we must parse the number
        -- of bytes to write out as well as the endianness of the write before
        -- parsing the additional arguments as Atoms.
        LCSE.depCons LCSC.nat $ \bytes ->
          LCSE.depCons LCSC.atomName $ \endiannessName ->
            case endiannessFromAtomName endiannessName of
              Just endianness ->
                case PN.mkNatRepr bytes of
                  Some bytesRepr | Just PN.LeqProof <- PN.isPosNat bytesRepr
                                 , Just PN.LeqProof <-
                                     PN.isPosNat (bytesToBits bytesRepr) -> do
                    let writeWrapper = buildPointerWriteWrapper bytesRepr
                                                                endianness
                    go (SomeExtensionWrapper writeWrapper)
                  _ -> empty
              Nothing -> empty
      LCSA.AtomName "bv-typed-literal" -> do
        -- Bitvector literals with a type argument are a special case.  We must
        -- parse the type argument separately before parsing the remaining
        -- argument as an Atom.
        LCSE.depCons (LCSC.extensionTypeParser hooks) $ \(Some tp) ->
          case tp of
            LCT.BVRepr{} ->
              go (SomeExtensionWrapper (buildBvTypedLitWrapper tp))
            _ -> empty
      _ ->
        case Map.lookup name wrappers of
          Nothing -> empty
          Just w -> go w
  where
    go (SomeExtensionWrapper wrapper) = do
      loc <- LCSE.position
      let ?parserHooks = hooks
      -- Generate atoms for the arguments to this extension
      operandAtoms <- LCSC.operands (extArgTypes wrapper)
      -- Pass these atoms to the extension wrapper and return an atom for the
      -- resulting value
      atomVal <- extWrapper wrapper operandAtoms
      let retType = LCCR.typeOfAtomValue atomVal
      endAtom <- LCSC.freshAtom loc atomVal
      return (Pair.Pair retType endAtom)

    -- Parse an 'LCSA.AtomName' representing an endianness into a
    -- 'Maybe DMM.Endianness'
    endiannessFromAtomName endianness =
      case endianness of
        LCSA.AtomName "le" -> Just DMM.LittleEndian
        LCSA.AtomName "be" -> Just DMM.BigEndian
        _ -> Nothing


-- | A wrapper for a syntax extension statement
--
-- Note that these are pure and are intended to guide the substitution of syntax
-- extensions for operations in the 'MDS.MacawExt' syntax.
data ExtensionWrapper arch args ret =
  ExtensionWrapper { extName :: LCSA.AtomName
                  -- ^ Name of the syntax extension
                   , extArgTypes :: LCT.CtxRepr args
                  -- ^ Types of the arguments to the syntax extension
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

-- | Wrap a statement extension binary operator
binop :: (DMM.MemWidth w, KnownNat w, Monad m)
      => (  DMM.AddrWidthRepr w
         -> lhsType
         -> rhsType
         -> LCCE.StmtExtension ext (LCCR.Atom s) tp )
      -- ^ Binary operator
      -> lhsType
      -- ^ Left-hand side operand
      -> rhsType
      -- ^ Right-hand side operand
      -> m (LCCR.AtomValue ext s tp)
binop op lhs rhs =
  return (LCCR.EvalExt (op (DMC.addrWidthRepr WI.knownNat) lhs rhs))


-- | Wrap a syntax extension binary operator, converting a bitvector in the
-- right-hand side position to an 'LLVMPointerType' before wrapping.
--
-- Note: we could make this more general to accept any width bitvector offset
binopRhsBvToPtr :: ( ext ~ DMS.MacawExt arch
                   , ExtensionParser m ext s
                   , 1 <= w
                   , DMM.MemWidth w
                   , KnownNat w )
                => (  DMM.AddrWidthRepr w
                   -> lhsType
                   -> LCCR.Atom s (LCLM.LLVMPointerType w)
                   -> LCCE.StmtExtension ext (LCCR.Atom s) tp)
                -- ^ Binary operator taking an 'LLVMPointerType' in the
                -- right-hand side position
                -> lhsType
                -- ^ Left-hand side operand
                -> LCCR.Atom s (LCT.BVType w)
                -- ^ Right-hand side operand as a bitvector to convert to an
                -- 'LLVMPointerType'
                -> m (LCCR.AtomValue ext s tp)
binopRhsBvToPtr op p1 p2 = do
  toPtrAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr WI.knownNat p2)))
  binop op p1 toPtrAtom

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
  , extWrapper = \args -> Ctx.uncurryAssignment (binopRhsBvToPtr DMS.PtrAdd) args }

-- | Wrapper for the 'DMS.PtrSub' syntax extension that enables users to
-- subtract integer offsets from pointers:
--
-- > pointer-sub ptr offset
--
-- Note that the underlying macaw primitive allows the offset to be in either
-- position. This user-facing interface is more restrictive.
wrapPointerSub
  :: ( 1 <= w
     , KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCT.BVType w)
                      (LCLM.LLVMPointerType w)
wrapPointerSub = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-sub"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> LCT.BVRepr LCT.knownNat
  , extWrapper = \args -> Ctx.uncurryAssignment (binopRhsBvToPtr DMS.PtrSub) args }

-- | Compute the difference between two pointers in bytes using 'DMS.PtrSub'
pointerDiff :: ( w ~ DMC.ArchAddrWidth arch
               , ext ~ DMS.MacawExt arch
               , ExtensionParser m ext s
               , 1 <= w
               , KnownNat w
               , DMM.MemWidth w )
            => LCCR.Atom s (LCLM.LLVMPointerType w)
            -> LCCR.Atom s (LCLM.LLVMPointerType w)
            -> m (LCCR.AtomValue ext s (LCT.BVType w))
pointerDiff lhs rhs = do
  ptrRes <- binop DMS.PtrSub lhs rhs
  ptrAtom <- LCSC.freshAtom WP.InternalPos ptrRes
  -- 'DMS.PtrSub' of two pointers produces a bitvector (LLVMPointer with region
  -- 0) so 'DMS.PtrToBits' is safe here.
  return (LCCR.EvalApp (LCE.ExtensionApp (DMS.PtrToBits LCT.knownNat ptrAtom)))

-- | Wrapper for the 'DMS.PtrSub' syntax extension that enables users to
-- subtract pointers from pointers:
--
-- > pointer-diff ptr1 ptr2
wrapPointerDiff
  :: ( w ~ DMC.ArchAddrWidth arch
     , 1 <= w
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w )
                      (LCT.BVType w)
wrapPointerDiff = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-diff"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , extWrapper = \args -> Ctx.uncurryAssignment pointerDiff args }

-- | Wrapper for 'DMS.MacawNullPtr' to construct a null pointer.
--
-- > make-null
wrapMakeNull
  :: ( w ~ DMC.ArchAddrWidth arch
     , 1 <= w
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      Ctx.EmptyCtx
                      (LCLM.LLVMPointerType w)
wrapMakeNull = ExtensionWrapper
  { extName = LCSA.AtomName "make-null"
  , extArgTypes = Ctx.empty
  , extWrapper = \_ ->
      let nullptr = DMS.MacawNullPtr (DMC.addrWidthRepr WI.knownNat) in
      return (LCCR.EvalApp (LCE.ExtensionApp nullptr)) }

-- | Wrapper for the 'DMS.PtrEq' syntax extension that enables users to test
-- the equality of two pointers.
--
-- > pointer-eq ptr1 ptr2
wrapPointerEq
  :: ( 1 <= w
     , KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w)
                      LCT.BoolType
wrapPointerEq = ExtensionWrapper
 { extName = LCSA.AtomName "pointer-eq"
 , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                           Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
 , extWrapper = \args -> Ctx.uncurryAssignment (binop DMS.PtrEq) args }

-- | Wrapper for the 'DMS.MacawReadMem' syntax extension that enables users to
-- read through a pointer to retrieve a bitvector of data at the underlying
-- memory location.
--
-- > pointer-read bytes endianness ptr
buildPointerReadWrapper
  :: ( 1 <= w
     , KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     , 1 <= sz
     , 1 <= (8 WI.* sz) )
  => WI.NatRepr sz
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                      (LCT.BVType (8 WI.* sz))
buildPointerReadWrapper bytes endianness = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-read"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , extWrapper =
      \args -> Ctx.uncurryAssignment (pointerRead bytes endianness) args }

-- | Read through a pointer using 'DMS.MacawReadMem'.
pointerRead :: ( w ~ DMC.ArchAddrWidth arch
               , DMM.MemWidth w
               , KnownNat w
               , ExtensionParser m ext s
               , ext ~ DMS.MacawExt arch
               , 1 <= sz
               , 1 <= (8 WI.* sz) )
            => WI.NatRepr sz
            -> DMM.Endianness
            -> LCCR.Atom s (LCLM.LLVMPointerType w)
            -> m (LCCR.AtomValue ext s (LCT.BVType (8 WI.* sz)))
pointerRead bytes endianness ptr = do
  let readInfo = DMC.BVMemRepr bytes endianness
  let bits = bytesToBits bytes
  let readExt = DMS.MacawReadMem (DMC.addrWidthRepr WI.knownNat) readInfo ptr
  readAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalExt readExt)
  return (LCCR.EvalApp (LCE.ExtensionApp (DMS.PtrToBits bits readAtom)))

-- | Wrapper for the 'DMS.MacawWriteMem' syntax extension that enables users to
-- write a bitvector of data through a pointer to the underlying memory
-- location.
--
-- > pointer-write bytes endianness ptr bitvector
buildPointerWriteWrapper
  :: ( w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , KnownNat w
     , ext ~ DMS.MacawExt arch
     , 1 <= sz
     , 1 <= (8 WI.* sz) )
  => WI.NatRepr sz
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCT.BVType (8 WI.* sz))
                      LCT.UnitType
buildPointerWriteWrapper bytes endianness = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-write"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> LCT.BVRepr (bytesToBits bytes)
  , extWrapper =
      \args -> Ctx.uncurryAssignment (pointerWrite bytes endianness) args }

-- | Read through a pointer using 'DMS.MacawWriteMem'.
pointerWrite :: ( w ~ DMC.ArchAddrWidth arch
                , DMM.MemWidth w
                , KnownNat w
                , ExtensionParser m ext s
                , ext ~ DMS.MacawExt arch
                , 1 <= sz
                , 1 <= (8 WI.* sz) )
              => WI.NatRepr sz
              -> DMM.Endianness
              -> LCCR.Atom s (LCLM.LLVMPointerType w)
              -> LCCR.Atom s (LCT.BVType (8 WI.* sz))
              -> m (LCCR.AtomValue ext s LCT.UnitType)
pointerWrite bytes endianness ptr val = do
  let bits = bytesToBits bytes
  toPtrAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr bits val)))
  let writeInfo = DMC.BVMemRepr bytes endianness
  let writeExt = DMS.MacawWriteMem (DMC.addrWidthRepr WI.knownNat)
                                   writeInfo
                                   ptr
                                   toPtrAtom
  return (LCCR.EvalExt writeExt)

-- | Wrapper for constructing bitvector literals matching the size of an
-- 'LCT.BVRepr'.  This enables users to instantiate literals with portable
-- types (such as SizeT).
--
-- > bv-typed-literal type integer
buildBvTypedLitWrapper
  :: LCT.TypeRepr (LCT.BVType w)
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCT.IntegerType)
                      (LCT.BVType w)
buildBvTypedLitWrapper tp = ExtensionWrapper
  { extName = LCSA.AtomName "bv-typed-literal"
  , extArgTypes = Ctx.empty Ctx.:> LCT.IntegerRepr
  , extWrapper = \args -> Ctx.uncurryAssignment (bvTypedLit tp) args }

-- | Create a bitvector literal matching the size of an 'LCT.BVRepr'
bvTypedLit :: forall s ext w m
           . ( ExtensionParser m ext s )
          => LCT.TypeRepr (LCT.BVType w)
          -> LCCR.Atom s LCT.IntegerType
          -> m (LCCR.AtomValue ext s (LCT.BVType w))
bvTypedLit (LCT.BVRepr w) val = return (LCCR.EvalApp (LCE.IntegerToBV w val))

-- | Syntax extension wrappers
extensionWrappers
  :: (w ~ DMC.ArchAddrWidth arch, 1 <= w, KnownNat w, DMC.MemWidth w)
  => Map.Map LCSA.AtomName (SomeExtensionWrapper arch)
extensionWrappers = Map.fromList
  [ (LCSA.AtomName "pointer-add", SomeExtensionWrapper wrapPointerAdd)
  , (LCSA.AtomName "pointer-diff", SomeExtensionWrapper wrapPointerDiff)
  , (LCSA.AtomName "pointer-sub", SomeExtensionWrapper wrapPointerSub)
  , (LCSA.AtomName "pointer-eq", SomeExtensionWrapper wrapPointerEq)
  , (LCSA.AtomName "make-null", SomeExtensionWrapper wrapMakeNull)
  ]

-- | All of the crucible syntax extensions to support machine code
machineCodeParserHooks
  :: forall w arch proxy
   . (w ~ DMC.ArchAddrWidth arch, 1 <= w, KnownNat w, DMC.MemWidth w)
  => proxy arch
  -> TypeLookup
  -- ^ A lookup function from a 'TypeAlias' to the underlying Crucible type
  -- it represents.
  -> LCSC.ParserHooks (DMS.MacawExt arch)
machineCodeParserHooks proxy typeLookup =
  let TypeLookup lookupFn = typeLookup
      types = Map.fromList [ (LCSA.AtomName (DT.pack (show t)), lookupFn t)
                           | t <- allTypeAliases ] in
  LCSC.ParserHooks (extensionTypeParser types)
                   (extensionParser extensionWrappers (machineCodeParserHooks proxy typeLookup))
