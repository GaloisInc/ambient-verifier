{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Ambient.FunctionOverride.Extension (
    TypeAlias(..)
  , TypeLookup(..)
  , ExtensionParser
  , SomeExtensionWrapper(..)
  , extensionParser
  , extensionTypeParser
  , runOverrideTests
  , CrucibleSyntaxOverrides(..)
  , emptyCrucibleSyntaxOverrides
  , loadCrucibleSyntaxOverrides
  , OverrideMapParseError(..)
  , machineCodeParserHooks
  ) where

import           Control.Applicative ( Alternative(empty) )
import           Control.Monad ( void, unless )
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO(liftIO) )
import qualified Data.Aeson as DA
import qualified Data.Aeson.Key as DAK
import qualified Data.Aeson.KeyMap as DAKM
import qualified Data.ByteString as BS
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
import qualified Data.Traversable as Trav
import qualified Data.Vector as DV
import qualified Data.Vector.NonEmpty as NEV
import qualified Data.Yaml as DY
import           Data.Word ( Word64 )
import           GHC.TypeNats ( KnownNat, type (<=) )
import qualified Lumberjack as LJ
import qualified System.Directory as SD
import qualified System.FilePath as SF
import qualified System.FilePath.Glob as SFG
import qualified System.IO as IO
import qualified Text.Megaparsec as MP
import           Text.Read ( readMaybe )

import qualified Data.Macaw.Architecture.Info as DMA
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.CFG.Core as LCCC
import qualified Lang.Crucible.CFG.Expr as LCE
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.CFG.SSAConversion as LCCS
import qualified Lang.Crucible.FunctionHandle as LCF
import qualified Lang.Crucible.LLVM.Intrinsics as LCLI
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.SymIO as LCLS
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.SymIO as LCSy
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.Syntax.ExprParse as LCSE
import qualified Lang.Crucible.Syntax.SExpr as LCSS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP
import qualified What4.Protocol.Online as WPO

import qualified Ambient.Diagnostic as AD
import qualified Ambient.Exception as AE
import qualified Ambient.Extensions as AExt
import qualified Ambient.FunctionOverride as AF
import qualified Ambient.FunctionOverride.ArgumentMapping as AFA
import           Ambient.FunctionOverride.Extension.Types
import qualified Ambient.FunctionOverride.Overrides.ForwardDeclarations as AFOF
import qualified Ambient.Memory as AM
import qualified Ambient.Verifier.SymbolicExecution as AVS

-- | A list of every type alias.
allTypeAliases :: [TypeAlias]
allTypeAliases = [minBound .. maxBound]

-- | The raw, unvalidated contents of a user-specified @--overrides@ directory.
-- 'CrucibleSyntaxOverrides' is the post-validation counterpart to this data
-- type.
data RawSyntaxOverrides = RawSyntaxOverrides
  { cblFiles :: [FilePath]
    -- ^ The @.cbl@ files in the @function@ subdirectory.
  , functionAddressOverrides :: [(FilePath, Word64, WF.FunctionName)]
    -- ^ The @function address overrides@ map in the @overrides.yaml@ file.
    --   If there is no @overrides.yaml@ file or if the map is not present,
    --   this list is empty.
  , startupOverrides :: [WF.FunctionName]
    -- ^ The @startup overrides@ list in the @overrides.yaml@ file. If there is
    --   no @overrides.yaml@ file or if the list is not present, then this list
    --   will be empty.
  }

-- | Parse the @function address overrides@ map in an @overrides.yaml@ file. If
-- no such map is present, return an empty list.
parseOverrideMap ::
  forall m.
  CMC.MonadThrow m =>
  DA.Value ->
  m [(FilePath, Word64, WF.FunctionName)]
parseOverrideMap val = do
  obj <- asObject val
  case DAKM.lookup "function address overrides" obj of
    Nothing -> pure []
    Just ovsVal -> do
      ovsObj <- asObject ovsVal
      ovs <- Trav.for (DAKM.toList ovsObj) $ \(bin, binVal) ->
               parseFunctionAddressOverrides (DAK.toString bin) binVal
      pure $ concat ovs
  where
    parseFunctionAddressOverrides ::
      FilePath -> DA.Value -> m [(FilePath, Word64, WF.FunctionName)]
    parseFunctionAddressOverrides bin binVal = do
      binObj <- asObject binVal
      traverse (\(addrKey, fun) -> do
                 addr <- case readMaybe (DAK.toString addrKey) of
                           Just addr -> pure addr
                           Nothing -> CMC.throwM $ ExpectedAddress addrKey
                 funName <- asString fun
                 pure (bin, addr, WF.functionNameFromText funName))
               (DAKM.toList binObj)

-- | Parse the @startup overrides@ list in an @overrides.yaml@ file. If no such
-- list is present, return an empty list.
parseStartupOverrides ::
  CMC.MonadThrow m =>
  DA.Value ->
  m [WF.FunctionName]
parseStartupOverrides val = do
  obj <- asObject val
  case DAKM.lookup "startup overrides" obj of
    Nothing -> pure []
    Just ovsVal -> do
      ovsArr <- asArray ovsVal
      ovsArr' <- traverse (\fun -> do
                            funName <- asString fun
                            pure $ WF.functionNameFromText funName)
                          ovsArr
      pure $ DV.toList ovsArr'

-- | Assert that a JSON 'DA.Value' is an 'DA.Array'. If this is the case,
-- return the underlying array. Otherwise, throw an exception.
asArray :: CMC.MonadThrow m => DA.Value -> m DA.Array
asArray (DA.Array a) = pure a
asArray val          = CMC.throwM $ ExpectedArray val

-- | Assert that a JSON 'DA.Value' is a 'DA.String'. If this is the case,
-- return the underlying text. Otherwise, throw an exception.
asString :: CMC.MonadThrow m => DA.Value -> m DT.Text
asString (DA.String t) = pure t
asString val           = CMC.throwM $ ExpectedString val

-- | Assert that a JSON 'DA.Value' is an 'DA.Object'. If this is the case,
-- return the underlying object. Otherwise, throw an exception.
asObject :: CMC.MonadThrow m => DA.Value -> m DA.Object
asObject (DA.Object o) = pure o
asObject val           = CMC.throwM $ ExpectedObject val

-- | Check if the user-specified @--overrides@ directory exists. If it does,
-- return the contents of the directory as a 'RawSyntaxOverrides' vales.
findRawSyntaxOverrides
  :: FilePath
  -> IO RawSyntaxOverrides
findRawSyntaxOverrides dirPath = do
  dirExists <- SD.doesDirectoryExist dirPath
  unless dirExists $ do
    CMC.throwM (AE.CrucibleOverrideDirectoryNotFound dirPath)
  cbls <- SFG.glob (dirPath SF.</> "function" SF.</> "*.cbl")
  let overridesYamlPath = dirPath SF.</> "overrides.yaml"
  overridesYamlExists <- SD.doesFileExist overridesYamlPath
  mbOverridesYaml <-
    if overridesYamlExists
      then do bytes <- BS.readFile overridesYamlPath
              val <- DY.decodeThrow bytes
              pure $ Just val
      else pure Nothing
  funAddrOvs <- maybe (pure []) parseOverrideMap mbOverridesYaml
  startupOvs <- maybe (pure []) parseStartupOverrides mbOverridesYaml
  pure $ RawSyntaxOverrides
           { cblFiles = cbls
           , functionAddressOverrides = funAddrOvs
           , startupOverrides = startupOvs
           }


-- | Read and parse a single crucible syntax override file.
loadCrucibleSyntaxOverride
  :: LCCE.IsSyntaxExtension ext
  => FilePath
  -- ^ Path to .cbl file to load
  -> Nonce.NonceGenerator IO s
  -> LCF.HandleAllocator
  -> LCSC.ParserHooks ext
  -- ^ ParserHooks for the desired syntax extension
  -> IO (LCSC.ParsedProgram ext)
loadCrucibleSyntaxOverride path ng halloc hooks = do
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
      eAcfgs <- LCSC.top ng halloc [] $ LCSC.prog asts
      case eAcfgs of
        Left err -> CMC.throwM (AE.CrucibleSyntaxExprParseFailure err)
        Right parsedProg -> pure parsedProg

-- | Run tests for crucible syntax function overrides.  This function reads all
-- files matching @<dirPath>/function/*.cbl@ and symbolically executes any
-- function with a name starting with @test_@.
runOverrideTests :: forall ext s sym bak arch w solver scope st fs p
                  . ( ?memOpts :: LCLM.MemOptions
                    , LCLM.HasLLVMAnn sym
                    , ext ~ DMS.MacawExt arch
                    , LCCE.IsSyntaxExtension ext
                    , LCB.IsSymBackend sym bak
                    , sym ~ WE.ExprBuilder scope st fs
                    , bak ~ LCBO.OnlineBackend solver scope st fs
                    , WPO.OnlineSolver solver
                    , p ~ AExt.AmbientSimulatorState sym arch
                    , w ~ DMC.ArchAddrWidth arch
                    , KnownNat w
                    , DMM.MemWidth w
                    , 1 <= w
                    , 16 <= w
                    )
                 => LJ.LogAction IO AD.Diagnostic
                 -> bak
                 -> DMA.ArchitectureInfo arch
                 -> DMS.GenArchVals DMS.LLVMMemory arch
                 -> AF.BuildFunctionABI arch sym p
                 -> AM.InitArchSpecificGlobals arch
                 -> FilePath
                 -- ^ Override directory
                 -> Nonce.NonceGenerator IO s
                 -> LCF.HandleAllocator
                 -> LCSC.ParserHooks ext
                 -- ^ ParserHooks for the desired syntax extension
                 -> IO ()
runOverrideTests logAction bak archInfo archVals (AF.BuildFunctionABI buildFunctionABI)
                 initGlobals dirPath ng halloc hooks = do
  RawSyntaxOverrides{cblFiles} <- findRawSyntaxOverrides dirPath
  loadedProgs <-
    traverse (\path -> (path,) <$> loadCrucibleSyntaxOverride path ng halloc hooks)
             cblFiles
  cblNameOvs <-
    traverse
      (\(path, parsedProg) -> parsedProgToFunctionOverride path parsedProg)
      loadedProgs
  mapM_ (\(path, parsedProg) -> runTests cblNameOvs path parsedProg) loadedProgs
  where
    sym = LCB.backendGetSym bak

    -- | Run all of the @test_@ functions in a @.cbl@ file.
    runTests ::
      [AF.SomeFunctionOverride p sym ext] ->
      -- ^ The @<name>@ function overrides defined in each @<name>.cbl@ file.
      FilePath ->
      -- ^ The @.cbl@ file path
      LCSC.ParsedProgram ext ->
      -- ^ The parsed contents of the @.cbl@ file
      IO ()
    runTests cblNameOvs path parsedProg = do
      let ovGlobals = parsedProgGlobalsList parsedProg
      let (matchCFGs, auxCFGs) = List.partition hasTestName
                                   (LCSC.parsedProgCFGs parsedProg)
      let fwdDecsMap = LCSC.parsedProgForwardDecs parsedProg
      mapM_ (runOneTest path ovGlobals auxCFGs fwdDecsMap cblNameOvs) matchCFGs

    -- Run a single @test_@ function in a @.cbl@ file.
    runOneTest :: FilePath
               -> [Some LCS.GlobalVar]
               -> [LCSC.ACFG ext]
               -> Map.Map WF.FunctionName LCF.SomeHandle
               -> [AF.SomeFunctionOverride p sym ext]
               -> LCSC.ACFG ext
               -> IO ()
    runOneTest path ovGlobals auxCFGs fwdDecsMap cblNameOvs acfg = do
      LJ.writeLog logAction (AD.ExecutingOverrideTest acfg path)
      case acfg of
        LCSC.ACFG Ctx.Empty LCT.UnitRepr test -> do
          let testHdl = LCCR.cfgHandle test
          -- Because we are testing outside of a binary, the choice of memory
          -- image is unimportant.
          let mem = DMM.emptyMemory (DMA.archAddrWidth archInfo)
          initMem <- AVS.initializeMemory
                       bak
                       halloc
                       archInfo
                       (NEV.singleton mem)
                       initGlobals
                       cblNameOvs
                       Map.empty -- Because we are testing outside of a binary,
                                 -- there are no binary-specific global
                                 -- variables to add.
          let ?ptrWidth = WI.knownNat @(DMC.ArchAddrWidth arch)
          (fs, _, LCLS.SomeOverrideSim _initFSOverride) <- liftIO $
            LCLS.initialLLVMFileSystem halloc sym WI.knownRepr
              -- For now, we always use an empty symbolic filesystem. We may
              -- want to reconsider this choice if we want to test overrides
              -- that call functions like `readFile`.
              LCSy.emptyInitialFileSystemContents
              [] (AM.imGlobals initMem)
          let functionABI =
                buildFunctionABI
                  AF.TestContext fs initMem archVals
                  Map.empty -- Because we are testing outside of a binary, we
                            -- need not concern ourselves with which
                            -- relocations are not supported.
                  Map.empty -- Because we are testing outside of a binary, we
                            -- cannot invoke function addresses, so we do not
                            -- need to register any function address overrides.
                  cblNameOvs
          fwdDecBindings <- resolveForwardDecs (AF.functionNameMapping functionABI) fwdDecsMap
          -- Make sure to also include functions that don't begin with `test_`
          -- (i.e., the `auxCFGs`), as they might be used during simulation.
          -- For example, if our test function is named @test_foobar, we'll
          -- need to include the CFG for @foobar itself.
          let fns = LCS.fnBindingsFromList $
                    fwdDecBindings ++ map acfgToFnBinding (acfg : auxCFGs)
          DMS.withArchEval archVals sym $ \archEvalFn -> do
            let fnLookup = DMS.unsupportedFunctionCalls "Ambient override tests"
            let syscallLookup = DMS.unsupportedSyscalls "Ambient override tests"
            let extImpl = AExt.ambientExtensions bak
                                                 archEvalFn
                                                 initMem
                                                 fnLookup
                                                 syscallLookup
                                                 Map.empty
            let ctx = LCS.initSimContext bak
                                         LCLI.llvmIntrinsicTypes
                                         halloc
                                         IO.stdout
                                         fns
                                         extImpl
                                         AExt.emptyAmbientSimulatorState
            let simAction = LCS.runOverrideSim LCT.UnitRepr
                                               (LCS.regValue <$> LCS.callFnVal (LCS.HandleFnVal testHdl) LCS.emptyRegMap)
            globals1 <- AVS.insertFreshGlobals sym ovGlobals (AM.imGlobals initMem)
            let s0 = LCS.InitialState ctx
                                      globals1
                                      LCS.defaultAbortHandler
                                      LCT.UnitRepr
                                      simAction
            void $ LCS.executeCrucible [] s0
        LCSC.ACFG _ _ g ->
          let fnName = LCF.handleName (LCCR.cfgHandle g) in
          CMC.throwM (AE.IllegalCrucibleSyntaxTestSignature path fnName)

    -- Construct function bindings for any forward declarations. See
    -- Note [Resolving forward declarations] in
    -- Ambient.FunctionOverride.Overrides.ForwardDeclarations.
    resolveForwardDecs ::
      Map.Map WF.FunctionName (AF.SomeFunctionOverride p sym ext) ->
      Map.Map WF.FunctionName LCF.SomeHandle ->
      IO [LCS.FnBinding p sym ext]
    resolveForwardDecs functionNameMapping fwdDecsMap =
      traverse (\(fwdDecName, LCF.SomeHandle fwdDecHandle) ->
                 do ovSim <- AFOF.mkForwardDeclarationOverride
                               bak functionNameMapping fwdDecName fwdDecHandle
                    pure $ LCS.FnBinding fwdDecHandle $ LCS.UseOverride ovSim)
               (Map.toAscList fwdDecsMap)

-- | Load all crucible syntax function overrides in an @--overrides@ directory.
-- This function reads all files matching @<dirPath>/function/*.cbl@ and
-- generates 'AF.FunctionOverride's for them. It will also parse and validate
-- the @overrides.yaml@ file if one is present.
loadCrucibleSyntaxOverrides :: forall ext w s p sym
                             . (LCCE.IsSyntaxExtension ext, DMM.MemWidth w)
                            => FilePath
                            -- ^ Override directory
                            -> Nonce.NonceGenerator IO s
                            -> LCF.HandleAllocator
                            -> LCSC.ParserHooks ext
                            -- ^ ParserHooks for the desired syntax extension
                            -> IO (CrucibleSyntaxOverrides w p sym ext)
                            -- ^ The loaded overrides
loadCrucibleSyntaxOverrides dirPath ng halloc hooks = do
  RawSyntaxOverrides{cblFiles, functionAddressOverrides, startupOverrides}
    <- findRawSyntaxOverrides dirPath
  namedOvs <- traverse go cblFiles
  let namedOvsMap = Map.fromList $
        map (\sov@(AF.SomeFunctionOverride ov) -> (AF.functionName ov, sov))
            namedOvs
  startupOvs <- traverse (\funName ->
                           case Map.lookup funName namedOvsMap of
                             Just ov -> validateStartupOverride ov
                             Nothing -> CMC.throwM $ AE.StartupOverrideNameNotFound funName)
                         startupOverrides
  funAddrOvs <- traverse (\(bin, addr, funName) ->
                           let addrMemWord = fromIntegral addr in
                           case Map.lookup funName namedOvsMap of
                             Just ov -> pure (AF.AddrInBinary addrMemWord bin, ov)
                             Nothing -> CMC.throwM $ AE.FunctionAddressOverridesNameNotFound
                                          bin addrMemWord funName)
                         functionAddressOverrides
  pure $ CrucibleSyntaxOverrides
    { csoAddressOverrides = Map.fromList funAddrOvs
    , csoStartupOverrides = startupOvs
    , csoNamedOverrides = namedOvs
    }
  where
    -- Given a @<name>.cbl@ file, return an override for the @<name>@ function.
    go :: FilePath -> IO (AF.SomeFunctionOverride p sym ext)
    go path = do
      parsedProg <- loadCrucibleSyntaxOverride path ng halloc hooks
      parsedProgToFunctionOverride path parsedProg

    -- Validate that a startup override has no arguments and returns @Unit@.
    validateStartupOverride ::
      AF.SomeFunctionOverride p sym ext ->
      IO (AF.FunctionOverride p sym Ctx.EmptyCtx ext LCT.UnitType)
    validateStartupOverride (AF.SomeFunctionOverride ov)
      | Just WI.Refl <- WI.testEquality (AF.functionArgTypes ov) Ctx.Empty
      , Just WI.Refl <- WI.testEquality (AF.functionReturnType ov) LCT.UnitRepr
      = pure ov

      | otherwise
      = CMC.throwM $ AE.StartupOverrideUnexpectedType $ AF.functionName ov

-- | Convert a 'LCSC.ParsedProgram' at a the given 'FilePath' to a function
-- override.
parsedProgToFunctionOverride ::
  FilePath ->
  LCSC.ParsedProgram ext ->
  IO (AF.SomeFunctionOverride p sym ext)
parsedProgToFunctionOverride path parsedProg = do
  let fnName = DS.fromString $ SF.takeBaseName path
  let globals = parsedProgGlobalsList parsedProg
  let (matchCFGs, auxCFGs) = List.partition (hasSameNameAsCblFile path)
                                            (LCSC.parsedProgCFGs parsedProg)
  let fwdDecs = LCSC.parsedProgForwardDecs parsedProg
  case matchCFGs of
    [] -> CMC.throwM (AE.CrucibleSyntaxFunctionNotFound fnName path)
    [acfg] ->
      return $ acfgToFunctionOverride fnName globals fwdDecs auxCFGs acfg
    _ ->
      -- This shouldn't be possible.  Multiple functions with the same name
      -- should have already been caught by crucible-syntax.
      CMC.throwM $ AE.DuplicateNamesInCrucibleOverride path fnName

-- Convert an ACFG to a FunctionOverride
acfgToFunctionOverride
  :: WF.FunctionName
  -> [ Some LCS.GlobalVar ]
  -- ^ GlobalVars used in function override
  -> Map.Map WF.FunctionName LCF.SomeHandle
  -- ^ Forward declarations declared in the override
  -> [LCSC.ACFG ext]
  -- ^ The ACFGs for auxiliary functions
  -> LCSC.ACFG ext
  -> AF.SomeFunctionOverride p sym ext
acfgToFunctionOverride name globals fwdDecs auxCFGs (LCSC.ACFG argTypes retType cfg) =
  let argMap = AFA.bitvectorArgumentMapping argTypes
      (ptrTypes, ptrTypeMapping) = AFA.pointerArgumentMappping argMap
      retRepr = AFA.promoteBVToPtr retType
  in case LCCS.toSSA cfg of
       LCCC.SomeCFG ssaCfg ->
         AF.SomeFunctionOverride $ AF.FunctionOverride
         { AF.functionName = name
         , AF.functionGlobals = globals
         , AF.functionArgTypes = ptrTypes
         , AF.functionReturnType = retRepr
         , AF.functionAuxiliaryFnBindings = map acfgToFnBinding auxCFGs
         , AF.functionForwardDeclarations = fwdDecs
           -- Note that we do not use the GetVarArg callback below since syntax
           -- overrides do not have a mechanism for variadic arguments. See
           -- Note [Varargs] in Ambient.FunctionOverride.
         , AF.functionOverride = \bak args _getVarArg -> do
             -- Translate any arguments that are LLVMPointers but should be Bitvectors into Bitvectors
             --
             -- This generates side conditions asserting that the block ID is zero
             pointerArgs <- liftIO $ AFA.buildFunctionOverrideArgs bak argMap ptrTypeMapping args
             userRes <- LCS.callCFG ssaCfg (LCS.RegMap pointerArgs)
             -- Convert any BV returns from the user override to LLVMPointers
             LCS.regValue <$> liftIO (AFA.convertBitvector bak retRepr userRes)
         }

-- | Convert an 'LCSC.ACFG' to a 'LCS.FnBinding'.
acfgToFnBinding :: forall p sym ext. LCSC.ACFG ext -> LCS.FnBinding p sym ext
acfgToFnBinding (LCSC.ACFG _ _ g) =
  case LCCS.toSSA g of
    LCCC.SomeCFG ssa ->
      LCS.FnBinding (LCCR.cfgHandle g)
                    (LCS.UseCFG ssa (LCAP.postdomInfo ssa))

-- | Retrieve the 'WF.FunctionName' in the handle in a 'LCSC.ACFG'.
acfgHandleName :: LCSC.ACFG ext -> WF.FunctionName
acfgHandleName (LCSC.ACFG _ _ g) = LCF.handleName (LCCR.cfgHandle g)

-- | Retrieve the global variables in a 'LSCS.ParsedProgram' in list form.
parsedProgGlobalsList :: LCSC.ParsedProgram ext -> [Some LCS.GlobalVar]
parsedProgGlobalsList (LCSC.ParsedProgram{LCSC.parsedProgGlobals = globals}) =
  [ Some glob
  | (_, (Pair.Pair _ glob)) <- Map.toList globals ]

-- | Does a function's name begin with @test_@?
hasTestName :: LCSC.ACFG ext -> Bool
hasTestName acfg = List.isPrefixOf "test_" $ show $ acfgHandleName acfg

-- | Does a function have the same name as the @.cbl@ file in which it is
-- defined?
hasSameNameAsCblFile :: FilePath -> LCSC.ACFG ext -> Bool
hasSameNameAsCblFile path acfg =
  acfgHandleName acfg == DS.fromString (SF.takeBaseName path)

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

-- | Check that a 'WI.NatRepr' containing a value in bits is a multiple of 8.
-- If so, pass the result of the value divided by 8 (i.e., as bytes) to the
-- continuation. Otherwise, return a default result.
bitsToBytes ::
  WI.NatRepr bits ->
  a ->
  -- ^ Default value to use if @bits@ is not a multiple of 8
  (forall bytes. ((8 WI.* bytes) ~ bits) => WI.NatRepr bytes -> a) ->
  -- ^ Continuation to invoke is @bits@ is a multiple of 8
  a
bitsToBytes bitsRep nonMultipleOf8 multipleOf8 =
  PN.withDivModNat bitsRep w8 $ \bytesRep modRep ->
    case PN.isZeroNat modRep of
      PN.NonZeroNat -> nonMultipleOf8
      PN.ZeroNat
        |  PN.Refl <- PN.mulComm bytesRep w8
        -> multipleOf8 bytesRep
  where
    w8 = PN.knownNat @8

-- | Perform a case analysis on the type argument to @pointer-read@ or
-- @pointer-write@. If the supplied type is not supported, return 'empty'.
-- This function packages factors out all of the grungy pattern-matching and
-- constraint wrangling that @pointer-read@ and @pointer-write@ share in
-- common.
withSupportedPointerReadWriteTypes ::
  Alternative f =>
  LCT.TypeRepr tp ->
  -- ^ The type argument
  (forall bits bytes.
     ( tp ~ LCT.BVType bits
     , (8 WI.* bytes) ~ bits
     , 1 <= bits
     , 1 <= bytes
     ) =>
     WI.NatRepr bits ->
     WI.NatRepr bytes ->
     f a) ->
  -- ^ Continuation to use if the argument is @'LCT.BVRepr (8 'WI.*' bytes)@
  -- (for some positive number @bytes@).
  (forall bits bytes.
     ( tp ~ LCLM.LLVMPointerType bits
     , (8 WI.* bytes) ~ bits
     , 1 <= bits
     , 1 <= bytes
     ) =>
     WI.NatRepr bits ->
     WI.NatRepr bytes ->
     f a) ->
  -- ^ Continuation to use if the argument is
  -- @'LCLM.LLVMPointerRepr (8 'WI.*' bytes)@ (for some positive number
  -- @bytes@).
  f a
withSupportedPointerReadWriteTypes tp bvK ptrK =
  case tp of
    LCT.BVRepr bits ->
      bitsToBytes bits empty $ \bytes ->
        case PN.isPosNat bytes of
          Nothing -> empty
          Just PN.LeqProof -> bvK bits bytes
    LCLM.LLVMPointerRepr bits ->
      bitsToBytes bits empty $ \bytes ->
        case PN.isPosNat bytes of
          Nothing -> empty
          Just PN.LeqProof -> ptrK bits bytes
    _ -> empty

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
  let ?parserHooks = hooks in
  LCSE.depCons LCSC.atomName $ \name ->
    case name of
      LCSA.AtomName "pointer-read" -> do
        -- Pointer reads are a special case because we must parse the type of
        -- the value to read as well as the endianness of the read before
        -- parsing the additional arguments as Atoms.
        LCSE.depCons LCSC.isType $ \(Some tp) ->
          LCSE.depCons LCSC.atomName $ \endiannessName ->
            case endiannessFromAtomName endiannessName of
              Just endianness ->
                let readWrapper =
                      buildPointerReadWrapper tp endianness in
                go (SomeExtensionWrapper readWrapper)
              Nothing -> empty
      LCSA.AtomName "pointer-write" -> do
        -- Pointer writes are a special case because we must parse the type of
        -- the value to write out as well as the endianness of the write before
        -- parsing the additional arguments as Atoms.
        LCSE.depCons LCSC.isType $ \(Some tp) ->
          LCSE.depCons LCSC.atomName $ \endiannessName ->
            case endiannessFromAtomName endiannessName of
              Just endianness ->
                let writeWrapper =
                      buildPointerWriteWrapper tp endianness in
                go (SomeExtensionWrapper writeWrapper)
              Nothing -> empty
      LCSA.AtomName "bv-typed-literal" -> do
        -- Bitvector literals with a type argument are a special case.  We must
        -- parse the type argument separately before parsing the remaining
        -- argument as an Atom.
        LCSE.depCons LCSC.isType $ \(Some tp) ->
          case tp of
            LCT.BVRepr{} ->
              go (SomeExtensionWrapper (buildBvTypedLitWrapper tp))
            _ -> empty
      _ ->
        case Map.lookup name wrappers of
          Nothing -> empty
          Just w -> go w
  where
    go :: (?parserHooks :: LCSC.ParserHooks ext)
       => SomeExtensionWrapper arch
       -> m (Pair.Pair LCT.TypeRepr (LCCR.Atom s))
    go (SomeExtensionWrapper wrapper) = do
      loc <- LCSE.position
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

-- | Wrap a statement extension binary operator
binop :: (KnownNat w, Monad m)
      => (  WI.NatRepr w
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
  return (LCCR.EvalExt (op WI.knownNat lhs rhs))


-- | Wrap a syntax extension binary operator, converting a bitvector in the
-- right-hand side position to an 'LLVMPointerType' before wrapping.
binopRhsBvToPtr :: ( ext ~ DMS.MacawExt arch
                   , ExtensionParser m ext s
                   , 1 <= w
                   , KnownNat w )
                => (  WI.NatRepr w
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
  , extWrapper = \args -> Ctx.uncurryAssignment (binopRhsBvToPtr (DMS.PtrSub . DMM.addrWidthRepr)) args }

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
  ptrRes <- binop (DMS.PtrSub . DMM.addrWidthRepr) lhs rhs
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
 , extWrapper = \args -> Ctx.uncurryAssignment (binop (DMS.PtrEq . DMM.addrWidthRepr)) args }

-- | Wrapper for the 'DMS.MacawReadMem' syntax extension that enables users to
-- read through a pointer to retrieve data at the underlying memory location.
--
-- > pointer-read type endianness ptr
buildPointerReadWrapper
  :: ( 1 <= w
     , KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     )
  => LCT.TypeRepr tp
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                      tp
buildPointerReadWrapper tp endianness = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-read"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
  , extWrapper =
      \args -> Ctx.uncurryAssignment (pointerRead tp endianness) args }

-- | Read through a pointer using 'DMS.MacawReadMem'.
pointerRead :: ( w ~ DMC.ArchAddrWidth arch
               , DMM.MemWidth w
               , KnownNat w
               , ExtensionParser m ext s
               , ext ~ DMS.MacawExt arch
               )
            => LCT.TypeRepr tp
            -> DMM.Endianness
            -> LCCR.Atom s (LCLM.LLVMPointerType w)
            -> m (LCCR.AtomValue ext s tp)
pointerRead tp endianness ptr =
  withSupportedPointerReadWriteTypes tp
    (\bits bytes -> do -- `Bitvector w` case
      let readInfo = DMC.BVMemRepr bytes endianness
      let readExt = DMS.MacawReadMem (DMC.addrWidthRepr WI.knownNat) readInfo ptr
      readAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalExt readExt)
      return (LCCR.EvalApp (LCE.ExtensionApp (DMS.PtrToBits bits readAtom))))
    (\_bits bytes -> do -- `Pointer` case
      let readInfo = DMC.BVMemRepr bytes endianness
      let readExt = DMS.MacawReadMem (DMC.addrWidthRepr WI.knownNat) readInfo ptr
      return (LCCR.EvalExt readExt))

-- | Wrapper for the 'DMS.MacawWriteMem' syntax extension that enables users to
-- write data through a pointer to the underlying memory location.
--
-- > pointer-write type endianness ptr (val :: type)
buildPointerWriteWrapper
  :: ( w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , KnownNat w
     , ext ~ DMS.MacawExt arch
     )
  => LCT.TypeRepr tp
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> tp)
                      LCT.UnitType
buildPointerWriteWrapper tp endianness = ExtensionWrapper
  { extName = LCSA.AtomName "pointer-write"
  , extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> tp
  , extWrapper =
      \args -> Ctx.uncurryAssignment (pointerWrite tp endianness) args }

-- | Read through a pointer using 'DMS.MacawWriteMem'.
pointerWrite :: ( w ~ DMC.ArchAddrWidth arch
                , DMM.MemWidth w
                , KnownNat w
                , ExtensionParser m ext s
                , ext ~ DMS.MacawExt arch
                )
              => LCT.TypeRepr tp
              -> DMM.Endianness
              -> LCCR.Atom s (LCLM.LLVMPointerType w)
              -> LCCR.Atom s tp
              -> m (LCCR.AtomValue ext s LCT.UnitType)
pointerWrite tp endianness ptr val =
  withSupportedPointerReadWriteTypes tp
    (\bits bytes -> do -- `Bitvector w` case
      toPtrAtom <- LCSC.freshAtom WP.InternalPos
        (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr bits val)))
      let writeInfo = DMC.BVMemRepr bytes endianness
      let writeExt = DMS.MacawWriteMem (DMC.addrWidthRepr WI.knownNat)
                                       writeInfo
                                       ptr
                                       toPtrAtom
      return (LCCR.EvalExt writeExt))
    (\_bits bytes -> do -- `Pointer` case
      let writeInfo = DMC.BVMemRepr bytes endianness
      let writeExt = DMS.MacawWriteMem (DMC.addrWidthRepr WI.knownNat)
                                       writeInfo
                                       ptr
                                       val
      return (LCCR.EvalExt writeExt))

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
