{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | Various utilities for looking up symbols in ELF binaries.
module Ambient.Loader.ELF.Symbols
  ( elfDynamicFuncSymbolMap
  , elfEntryPointAddrMap
  , elfEntryPointSymbolMap
  , elfDynamicGlobalSymbolMap
  , symtabEntryFunctionName
  , versionTableValueToSymbolVersion
  ) where

import qualified Control.Exception as X
import           Control.Monad ( guard )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit as DE
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe, listToMaybe )
import qualified Data.Text.Encoding as DTE
import qualified Data.Text.Encoding.Error as DTEE
import qualified Data.Vector as DV
import           Data.Word ( Word32 )

import qualified Data.BinarySymbols as BinSym
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.BinaryLoader.ELF as DMBE
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.LoadCommon as DMML
import qualified What4.FunctionName as WF

import qualified Ambient.Exception as AE
import qualified Ambient.Loader.Versioning as ALV
import qualified Ambient.Panic as AP

-- | Given a collection of binaries, map the name of each dynamic function to
-- its address. (See 'isFuncSymbol' for a precise definition of
-- \"dynamic function\".)
--
-- This checks that each dynamic function's name is unique across all binaries,
-- and if not, this function will throw an exception.

-- TODO: This check may be too strict in the presence of weak symbols. If this
-- is the case, we should establish a load order and respect weak symbols, only
-- throwing an exception if a symbol is /strongly/ defined more than once.
elfDynamicFuncSymbolMap ::
  forall f arch w.
  ( Foldable f
  , w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  ) =>
  f (DMB.LoadedBinary arch (DE.ElfHeaderInfo w)) ->
  IO (Map.Map ALV.VersionedFunctionName (DMM.MemWord w))
elfDynamicFuncSymbolMap = elfDynamicSymbolMap
  (\nm addr1 addr2 -> X.throwIO $ AE.DynamicFunctionNameClash nm addr1 addr2)
  symtabEntryFunctionName
  isFuncSymbol

-- | Return true if this symbol table entry corresponds to a
-- globally defined symbol.
--
-- Taken from reopt (https://github.com/GaloisInc/reopt), which is licensed
-- under the 3-Clause BSD license.
isGlobalSymbol :: DE.SymtabEntry nm w -> Bool
isGlobalSymbol e
  =  DE.steBind  e == DE.STB_GLOBAL
  && DE.steIndex e /= DE.SHN_UNDEF
  && DE.steIndex e <  DE.SHN_LORESERVE

-- | Return true if this symbol table entry corresponds to a
-- globally defined function.
--
-- Taken from reopt (https://github.com/GaloisInc/reopt), which is licensed
-- under the 3-Clause BSD license.
isFuncSymbol :: DE.SymtabEntry nm w -> Bool
isFuncSymbol e
  =  DE.steType  e == DE.STT_FUNC
  && isGlobalSymbol e

-- | Return true if this symbol table entry corresponds to a
-- globally defined variable.
isGlobalVar :: DE.SymtabEntry nm w -> Bool
isGlobalVar e
  =  DE.steType  e == DE.STT_OBJECT
  && isGlobalSymbol e

-- | Given a collection of binaries, filter dynamic symbols by @filterFn@ and
-- map the name of each symbol to its address.
elfDynamicSymbolMap ::
  forall f arch w symbol.
  ( Foldable f
  , w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  , Ord symbol
  ) =>
  (ALV.VersionedSymbol symbol -> DMM.MemWord w -> DMM.MemWord w -> IO (DMM.MemWord w)) ->
  -- ^ Function to run on collisions.  Takes the symbol name, and the two
  -- addresses the symbol maps to and returns the address the symbol should map
  -- to.
  (DE.SymtabEntry (BSC.ByteString) (DE.ElfWordType w) -> symbol) ->
  -- ^ Function to extract the symbol name from a SymtabEntry
  (DE.SymtabEntry (BSC.ByteString) (DE.ElfWordType w) -> Bool) ->
  -- ^ Filter function over SymtabEntries.  Only symbols for which this
  -- function returns True will be included in the returned map.
  f (DMB.LoadedBinary arch (DE.ElfHeaderInfo w)) ->
  -- ^ Binaries to build symbol map from
  IO (Map.Map (ALV.VersionedSymbol symbol) (DMM.MemWord w))
elfDynamicSymbolMap onCollision getSymbol filterFn = F.foldlM addSymbols Map.empty
  where
    addSymbols ::
      Map.Map (ALV.VersionedSymbol symbol) (DMM.MemWord w) ->
      DMB.LoadedBinary arch (DE.ElfHeaderInfo w) ->
      IO (Map.Map (ALV.VersionedSymbol symbol) (DMM.MemWord w))
    addSymbols m loadedBinary =
      F.foldlM insertM m binaryMap
      where
        elfHeaderInfo = DMB.originalBinary loadedBinary
        offset = fromMaybe 0 $ DMML.loadOffset $ DMB.loadOptions loadedBinary

        dynSymbolTable = concatMap DV.toList $ elfResolveDynamicSymbolVersions elfHeaderInfo
        binaryMap = DE.elfClassInstances (DE.headerClass (DE.header elfHeaderInfo)) $
                    [ ( fmap getSymbol versym
                      , fromIntegral (DE.steValue ste) + fromIntegral offset
                      )
                    | versym <- dynSymbolTable
                    , let ste = ALV.versymSymbol versym
                    , filterFn ste
                    ]

        insertM mp (k, insertVal) =
          case Map.lookup k mp of
            Just existingVal -> do
              newVal <- onCollision k insertVal existingVal
              return $ Map.insert k newVal mp
            Nothing -> return $ Map.insert k insertVal mp

elfDynamicGlobalSymbolMap ::
  forall f arch w.
  ( Foldable f
  , w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  ) =>
  f (DMB.LoadedBinary arch (DE.ElfHeaderInfo w)) ->
  IO (Map.Map ALV.VersionedGlobalVarName (DMM.MemWord w))
elfDynamicGlobalSymbolMap = elfDynamicSymbolMap
  (\nm addr1 addr2 -> X.throwIO $ AE.DynamicGlobalNameClash nm addr1 addr2)
  DE.steName
  isGlobalVar

-- | Given a binary, map the resolved address offset of each entry point
-- function to its name. This includes entry points in both the static and
-- dynamic symbol tables.
elfEntryPointAddrMap ::
  (w ~ DMC.ArchAddrWidth arch, DMM.MemWidth w) =>
  DMB.LoadedBinary arch (DE.ElfHeaderInfo w) ->
  Map.Map (DMM.MemSegmentOff w) ALV.VersionedFunctionName
elfEntryPointAddrMap loadedBinary =
  DE.elfClassInstances (DE.headerClass (DE.header elfHeaderInfo)) $
  Map.fromList [ ( case DMBE.resolveAbsoluteAddress mem addr of
                     Just addrOff -> addrOff
                     Nothing -> AP.panic AP.Loader "elfEntryPointAddrMap"
                                  ["Failed to resolve function address: " ++ show addr]
                 , fmap symtabEntryFunctionName versym
                 )
               | versym <- elfEntryPoints elfHeaderInfo
               , let ste = ALV.versymSymbol versym
               , let addr = fromIntegral (DE.steValue ste) + fromIntegral offset
               ]
  where
    mem = DMB.memoryImage loadedBinary
    elfHeaderInfo = DMB.originalBinary loadedBinary
    offset = fromMaybe 0 $ DMML.loadOffset $ DMB.loadOptions loadedBinary

-- | Given a binary, map the name of each entry point function to its address.
-- This includes entry points in both the static and dynamic symbol tables.
elfEntryPointSymbolMap ::
  (w ~ DMC.ArchAddrWidth arch, DMM.MemWidth w) =>
  DMB.LoadedBinary arch (DE.ElfHeaderInfo w) ->
  Map.Map WF.FunctionName (DMM.MemWord w)
elfEntryPointSymbolMap loadedBinary =
  DE.elfClassInstances (DE.headerClass (DE.header elfHeaderInfo)) $
  Map.fromList
    [ ( symtabEntryFunctionName ste
      , fromIntegral (DE.steValue ste) + fromIntegral offset
      )
    | versym <- elfEntryPoints elfHeaderInfo
    , let ste = ALV.versymSymbol versym
    ]
  where
    elfHeaderInfo = DMB.originalBinary loadedBinary
    offset = fromMaybe 0 $ DMML.loadOffset $ DMB.loadOptions loadedBinary

-- | Return all of the entry points from the static and dynamic symbol tables
-- of a function. Here, \"entry point\" refers to an ELF function symbol
-- ('DE.STT_FUNC') with a non-zero address.
elfEntryPoints ::
  (DE.ElfWidthConstraints w, DMM.MemWidth w) =>
  DE.ElfHeaderInfo w ->
  [VersionedSymtabEntry BS.ByteString (DE.ElfWordType w)]
elfEntryPoints elfHeaderInfo =
  filter (\versym -> let ste = ALV.versymSymbol versym
                  in DE.steType ste == DE.STT_FUNC
                  -- Somewhat surprisingly, there can be STT_FUNC entries whose
                  -- values are zero. See, for instance, the static symbol table in
                  -- tests/binaries/aarch32/main-args.exe. These won't resolve
                  -- properly, so filter them out.
                  && toInteger (DE.steValue ste) /= 0)
         (staticSymbolTable ++ dynSymbolTable)
  where
    staticSymbolTable = concatMap DV.toList $ elfResolveStaticSymbolVersions elfHeaderInfo
    dynSymbolTable    = concatMap DV.toList $ elfResolveDynamicSymbolVersions elfHeaderInfo

-- | Find and get static symbol table entries from an ELF binary along with
-- their versions (if present).
elfResolveStaticSymbolVersions ::
  forall w.
  DE.ElfHeaderInfo w ->
  Maybe (DV.Vector (VersionedSymtabEntry BS.ByteString (DE.ElfWordType w)))
elfResolveStaticSymbolVersions elfHeaderInfo = do
  res <- DE.decodeHeaderSymtab elfHeaderInfo
  entries <- case res of
    Left symtabError -> error $ show symtabError
    Right entries    -> return entries
  pure $ DV.map resolve $ DE.symtabEntries entries
  where
    -- This code was taken from macaw-base
    -- (https://github.com/GaloisInc/macaw/blob/e4b198ab2dd882e34690ed33056d5231b2d776bf/base/src/Data/Macaw/Memory/ElfLoader.hs#L407-L421),
    -- which is licensed under the 3-Clause BSD license.
    --
    -- TODO: This code would be a better fit for elf-edit.
    resolve ::
      DE.SymtabEntry BS.ByteString (DE.ElfWordType w) ->
      VersionedSymtabEntry BS.ByteString (DE.ElfWordType w)
    resolve sym =
      -- Look for '@' as it is used to separate symbol name from version information
      -- in object files.
      case BSC.findIndex (== '@') (DE.steName sym) of
        Just i ->
          let nm = DE.steName sym in
                  -- If "@@" appears in the symbol, this is a default versioned symbol
          let ver | i+1 < BSC.length nm, BSC.index nm (i+1) == '@' =
                      BinSym.ObjectDefaultSymbol (BSC.drop (i+2) nm)
                  -- Otherwise "@" appears in the symbol, and this is a non-default symbol.
                  | otherwise =
                      BinSym.ObjectNonDefaultSymbol (BSC.drop (i+1) nm) in
          ALV.VerSym { ALV.versymSymbol = sym { DE.steName = BSC.take i nm }
                     , ALV.versymVersion = ver
                     }
        Nothing ->
          ALV.VerSym { ALV.versymSymbol = sym
                     , ALV.versymVersion = BinSym.UnversionedSymbol
                     }

-- | Find and get dynamic symbol table entries from an ELF binary along with
-- their versions (if present).
elfResolveDynamicSymbolVersions ::
  DE.ElfHeaderInfo w ->
  Maybe (DV.Vector (VersionedSymtabEntry BS.ByteString (DE.ElfWordType w)))
elfResolveDynamicSymbolVersions elfHeaderInfo = DE.elfClassInstances elfClass $ do
  vam <- DE.virtAddrMap elfBytes elfPhdrs
  rawDynSec <- listToMaybe (DE.findSectionByName (BSC.pack ".dynamic") elf)

  let dynBytes = DE.elfSectionData rawDynSec
  dynSec <- case DE.dynamicEntries (DE.elfData elf) (DE.elfClass elf) dynBytes of
    Left _dynErr -> Nothing
    Right dynSec -> return dynSec

  vdefm <- case DE.dynVersionDefMap dynSec vam of
    Left _dynErr -> Nothing
    Right vm -> return vm

  vreqm <- case DE.dynVersionReqMap dynSec vam of
    Left _dynErr -> Nothing
    Right vm -> return vm

  entries <- elfDynamicSymbolTable elfHeader elfBytes elfShdrs
  DV.imapM (\idx entry ->
             case DE.dynSymEntry dynSec vam vdefm vreqm (fromIntegral idx) of
               Left _dynError -> Nothing
               Right (_, ver) -> return $
                 ALV.VerSym { ALV.versymSymbol = entry
                            , ALV.versymVersion = versionTableValueToSymbolVersion ver
                            })
           entries
  where
    (_, elf) = DE.getElf elfHeaderInfo
    elfHeader = DE.header elfHeaderInfo
    elfClass = DE.headerClass elfHeader
    elfBytes = DE.headerFileContents elfHeaderInfo
    elfPhdrs = DE.headerPhdrs elfHeaderInfo
    elfShdrs = DE.headerShdrs elfHeaderInfo

-- | Convert GNU versioning information for a dynamic symbol to a
-- 'BinSym.SymbolVersion'.
versionTableValueToSymbolVersion :: DE.VersionTableValue -> BinSym.SymbolVersion
versionTableValueToSymbolVersion DE.VersionLocal  = BinSym.UnversionedSymbol
versionTableValueToSymbolVersion DE.VersionGlobal = BinSym.UnversionedSymbol
versionTableValueToSymbolVersion (DE.VersionSpecific elfVer) =
  BinSym.VersionedSymbol (DE.verFile elfVer) (DE.verName elfVer)

-- | Find and get dynamic symbol table entries from an ELF binary.
--
-- Taken from macaw (https://github.com/GaloisInc/macaw), which is licensed
-- under the 3-Clause BSD license.

-- TODO: We should consider upstreaming this to elf-edit at some point. See
-- https://github.com/GaloisInc/macaw/issues/277.
elfDynamicSymbolTable ::
  DE.ElfHeader w ->
  BS.ByteString ->
  -- ^ File contents
  DV.Vector (DE.Shdr Word32 (DE.ElfWordType w)) ->
  -- ^ Section header table
  Maybe (DV.Vector (DE.SymtabEntry BS.ByteString (DE.ElfWordType w)))
elfDynamicSymbolTable hdr contents shdrs = DE.elfClassInstances cl $ do
  guard (DE.headerType hdr == DE.ET_DYN)
  symtab <-
    case DV.toList $ DV.filter (\s -> DE.shdrType s == DE.SHT_DYNSYM) shdrs of
      [symtab] -> Just symtab
      _        -> Nothing
  let strtabIdx = DE.shdrLink symtab
  strtab <- shdrs DV.!? fromIntegral strtabIdx
  let shdrData shdr = DE.slice (DE.shdrFileRange shdr) contents
  let symtabData = shdrData symtab
  let strtabData = shdrData strtab
  case DE.decodeSymtab cl dta strtabData symtabData of
    Left _ -> Nothing
    Right entries -> Just entries
  where
    cl  = DE.headerClass hdr
    dta = DE.headerData hdr

-- | Return the 'WF.FunctionName' for a symbol table entry. This assumes that
-- the symbol name is UTF-8–encoded.
symtabEntryFunctionName :: DE.SymtabEntry BS.ByteString w -> WF.FunctionName
symtabEntryFunctionName =
  WF.functionNameFromText . DTE.decodeUtf8With DTEE.lenientDecode . DE.steName

-- | A symbol table entry paired with a version.
type VersionedSymtabEntry nm w = ALV.VersionedSymbol (DE.SymtabEntry nm w)
