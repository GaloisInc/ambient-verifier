{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | Various utilities for looking up symbols in ELF binaries.
module Ambient.Loader.ELF.Symbols
  ( elfDynamicFuncSymbolMap
  , elfEntryPointAddrMap
  , elfEntryPointSymbolMap
  , elfGlobalSymbolMap
  , elfDynamicGlobalSymbolMap
  , symtabEntryFunctionName
  , versionTableValueToSymbolVersion
  ) where

import           Control.Monad ( guard )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit as DE
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as NEL
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

import qualified Ambient.Loader.Versioning as ALV
import qualified Ambient.Panic as AP

-- | Given a collection of binaries, map the name of each dynamic function to
-- its address. (See 'isFuncSymbol' for a precise definition of
-- \"dynamic function\".)
--
-- If multiple binaries define the same symbol, the symbol from the binary that
-- appears first in the collection will be chosen over the symbol from the
-- later binary. As a result, the order of the binaries in the collection will
-- determine the lookup scope, as described in @Note [Dynamic lookup scope]@ in
-- "Ambient.Loader.ELF.DynamicLoader".
elfDynamicFuncSymbolMap ::
  forall f arch w.
  ( Foldable f
  , w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  ) =>
  f (DMB.LoadedBinary arch (DE.ElfHeaderInfo w)) ->
  Map.Map ALV.VersionedFunctionName (DMM.MemWord w)
elfDynamicFuncSymbolMap = elfDynamicSymbolMap
  symtabEntryFunctionName
  isFuncSymbol

-- | Return true if this symbol table entry corresponds to a
-- globally defined symbol.
--
-- Taken from reopt (https://github.com/GaloisInc/reopt), which is licensed
-- under the 3-Clause BSD license.
isGlobalSymbol :: DE.SymtabEntry nm w -> Bool
isGlobalSymbol e
  =  DE.steBind  e `elem` [DE.STB_GLOBAL, DE.STB_WEAK] -- See Note [Weak symbols]
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
--
-- If multiple binaries define the same symbol, the symbol from the binary that
-- appears first in the collection will be chosen over the symbol from the
-- later binary. As a result, the order of the binaries in the collection will
-- determine the lookup scope, as described in @Note [Dynamic lookup scope]@ in
-- "Ambient.Loader.ELF.DynamicLoader".
elfDynamicSymbolMap ::
  forall f arch w symbol.
  ( Foldable f
  , w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  , Ord symbol
  ) =>
  (DE.SymtabEntry (BSC.ByteString) (DE.ElfWordType w) -> symbol) ->
  -- ^ Function to extract the symbol name from a SymtabEntry
  (DE.SymtabEntry (BSC.ByteString) (DE.ElfWordType w) -> Bool) ->
  -- ^ Filter function over SymtabEntries.  Only symbols for which this
  -- function returns True will be included in the returned map.
  f (DMB.LoadedBinary arch (DE.ElfHeaderInfo w)) ->
  -- ^ Binaries to build symbol map from
  Map.Map (ALV.VersionedSymbol symbol) (DMM.MemWord w)
elfDynamicSymbolMap getSymbol filterFn =
  fmap snd . F.foldl' addSymbols Map.empty
  where
    addSymbols ::
      Map.Map (ALV.VersionedSymbol symbol)
              (DE.SymtabEntry (BSC.ByteString) (DE.ElfWordType w), DMM.MemWord w) ->
      DMB.LoadedBinary arch (DE.ElfHeaderInfo w) ->
      Map.Map (ALV.VersionedSymbol symbol)
              (DE.SymtabEntry (BSC.ByteString) (DE.ElfWordType w), DMM.MemWord w)
    addSymbols m loadedBinary =
      F.foldl' (\m' (versym, addr) ->
                 addSymbolWithPriority (fmap getSymbol versym) (ALV.versymSymbol versym) addr m')
               m dynSymsAndAddrs
      where
        elfHeaderInfo = DMB.originalBinary loadedBinary
        offset = fromMaybe 0 $ DMML.loadOffset $ DMB.loadOptions loadedBinary

        dynSymbolTable = concatMap DV.toList $ elfResolveDynamicSymbolVersions elfHeaderInfo
        dynSymsAndAddrs =
          DE.elfClassInstances (DE.headerClass (DE.header elfHeaderInfo)) $
          [ ( versym
            , fromIntegral (DE.steValue ste) + fromIntegral offset
            )
          | versym <- dynSymbolTable
          , let ste = ALV.versymSymbol versym
          , filterFn ste
          ]

-- | Add a new @symbol@ (which has been derived from a 'DE.SymtabEntry' in some
-- way) and associated @v@ value to a 'Map.Map'. If the 'Map.Map' already
-- contains that @symbol@, the conflict is resolved as follows:
--
-- 1. Global symbols are favored over weak symbols. See @Note [Weak symbols]@.
--    (The only reason the 'Map.Map' includes a 'DE.SymtabEntry' in its range
--    is because we need to consult its 'DE.steBind' during this step.)
--
-- 2. Otherwise, favor the already-encountered @symbol@ over the new @symbol@.
--    This is what implements the lookup scope scheme described in
--    @Note [Dynamic lookup scope]@ in "Ambient.Loader.ELF.DynamicLoader".
addSymbolWithPriority ::
  Ord symbol =>
  symbol ->
  DE.SymtabEntry nm w ->
  v ->
  Map.Map symbol (DE.SymtabEntry nm w, v) ->
  Map.Map symbol (DE.SymtabEntry nm w, v)
addSymbolWithPriority newSym newSt newVal =
  Map.insertWith
    (\new@(newSte, _) old@(oldSte, _) ->
      if -- Step (1)
         |  DE.steBind oldSte == DE.STB_GLOBAL
         ,  DE.steBind newSte == DE.STB_WEAK
         -> old

         |  DE.steBind newSte == DE.STB_GLOBAL
         ,  DE.steBind oldSte == DE.STB_WEAK
         -> new

         -- Step (2)
         |  otherwise
         -> old)
    newSym (newSt, newVal)

-- | Given a collection of binaries, map the name of each dynamic global
-- variable to its address. (See 'isGlobalVar' for a precise definition of
-- \"global variable\".)
--
-- If multiple binaries define the same symbol, the symbol from the binary that
-- appears first in the collection will be chosen over the symbol from the
-- later binary. As a result, the order of the binaries in the collection will
-- determine the lookup scope, as described in @Note [Dynamic lookup scope]@ in
-- "Ambient.Loader.ELF.DynamicLoader".
elfDynamicGlobalSymbolMap ::
  forall f arch w.
  ( Foldable f
  , w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  ) =>
  f (DMB.LoadedBinary arch (DE.ElfHeaderInfo w)) ->
  Map.Map ALV.VersionedGlobalVarName (DMM.MemWord w)
elfDynamicGlobalSymbolMap = elfDynamicSymbolMap
  DE.steName
  isGlobalVar

-- | Given a binary, map the resolved address offset of each entry point
-- function to its symbol names. This includes entry points in both the static
-- and dynamic symbol tables.
--
-- Most of the time, each function address is only associated with a single
-- name, but it is certainly possible for an address to have multiple names.
-- For example, it is quite common for @libc@ implementations to have names
-- like @__open64@, @open64@, @__open@, and @open@ all refer to the same
-- address.
elfEntryPointAddrMap ::
  (w ~ DMC.ArchAddrWidth arch, DMM.MemWidth w) =>
  DMB.LoadedBinary arch (DE.ElfHeaderInfo w) ->
  Map.Map (DMM.MemSegmentOff w) (NEL.NonEmpty ALV.VersionedFunctionName)
elfEntryPointAddrMap loadedBinary =
  DE.elfClassInstances (DE.headerClass (DE.header elfHeaderInfo)) $
  Map.fromListWith
    -- If we encounter a function address that already has symbol names
    -- associated with it, prepend the new name to the front of the list.
    -- This choice doesn't have particularly deep ramifications; the only thing
    -- that it affects is what function symbols will be reported in @macaw@
    -- logs. See the Haddocks for A.Loader.BinaryConfig.lbpAddrSymMap for more
    -- details.
    (\new old -> new <> old)
    [ ( case DMBE.resolveAbsoluteAddress mem addr of
          Just addrOff -> addrOff
          Nothing -> AP.panic AP.Loader "elfEntryPointAddrMap"
                       ["Failed to resolve function address: " ++ show addr]
      , fmap symtabEntryFunctionName versym NEL.:| []
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
  elfSymbolMap symtabEntryFunctionName loadedBinary (elfEntryPoints elfHeaderInfo)
  where
    elfHeaderInfo = DMB.originalBinary loadedBinary

-- | Given a binary, map the name of each entry global symbol to its address.
-- This includes entry points in both the static and dynamic symbol tables.
elfGlobalSymbolMap ::
  (w ~ DMC.ArchAddrWidth arch, DMM.MemWidth w) =>
  DMB.LoadedBinary arch (DE.ElfHeaderInfo w) ->
  Map.Map BS.ByteString (DMM.MemWord w)
elfGlobalSymbolMap loadedBinary =
  DE.elfClassInstances (DE.headerClass (DE.header elfHeaderInfo)) $
  elfSymbolMap DE.steName loadedBinary (elfGlobalVars elfHeaderInfo)
  where
    elfHeaderInfo = DMB.originalBinary loadedBinary

-- | Given a list of symbols from a binary, insert each symbol into a map,
-- where the keys are the symbol names and the values are the corresponding
-- addresses. This generally favors symbols that appear earlier in the list,
-- with global symbols always given priority over weak symbols. (See the
-- Haddocks for 'addSymbolWithPriority' for more information.)
elfSymbolMap ::
  ( w ~ DMC.ArchAddrWidth arch
  , DMM.MemWidth w
  , Ord symbol
  ) =>
  (DE.SymtabEntry BS.ByteString (DE.ElfWordType w) -> symbol) ->
  -- ^ Function to extract the symbol name from a 'DE.SymtabEntry'
  DMB.LoadedBinary arch (DE.ElfHeaderInfo w) ->
  [VersionedSymtabEntry BS.ByteString (DE.ElfWordType w)] ->
  Map.Map symbol (DMM.MemWord w)
elfSymbolMap getSymbol loadedBinary symbols =
  DE.elfClassInstances (DE.headerClass (DE.header elfHeaderInfo)) $
  fmap snd $
  F.foldl'
    (\m (ste, addr) -> addSymbolWithPriority (getSymbol ste) ste addr m)
    Map.empty
    [ ( ste
      , fromIntegral (DE.steValue ste) + fromIntegral offset
      )
    | versym <- symbols
    , let ste = ALV.versymSymbol versym
    ]
  where
    elfHeaderInfo = DMB.originalBinary loadedBinary
    offset = fromMaybe 0 $ DMML.loadOffset $ DMB.loadOptions loadedBinary

-- | Return all of the entry points from the static and dynamic symbol tables
-- of a binary. Here, \"entry point\" refers to an ELF function symbol
-- ('DE.STT_FUNC') with a non-zero address.
elfEntryPoints ::
  (DE.ElfWidthConstraints w, DMM.MemWidth w) =>
  DE.ElfHeaderInfo w ->
  [VersionedSymtabEntry BS.ByteString (DE.ElfWordType w)]
elfEntryPoints = elfSymbols (\ste -> DE.steType ste == DE.STT_FUNC)

-- | Return all of the global variables from the static and dynamic symbol
-- tables of a binary. Here, \"global variable\" refers to an ELF object symbol
-- ('DE.STT_OBJECT') with a non-zero address.
elfGlobalVars ::
  (DE.ElfWidthConstraints w, DMM.MemWidth w) =>
  DE.ElfHeaderInfo w ->
  [VersionedSymtabEntry BS.ByteString (DE.ElfWordType w)]
elfGlobalVars = elfSymbols (\ste -> DE.steType ste == DE.STT_OBJECT)

-- | Return all of the non-zero-values symbol entry entries from the static and
-- dynamic symbol tables of a binary that satisfy some predicate.
elfSymbols ::
  (DE.ElfWidthConstraints w, DMM.MemWidth w) =>
  (DE.SymtabEntry BS.ByteString (DE.ElfWordType w) -> Bool) ->
  -- ^ Filter function over SymtabEntries.  Only symbols for which this
  -- function returns True will be included in the returned list.
  DE.ElfHeaderInfo w ->
  [VersionedSymtabEntry BS.ByteString (DE.ElfWordType w)]
elfSymbols filterFn elfHeaderInfo =
  filter (\versym -> let ste = ALV.versymSymbol versym
                  in filterFn ste
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

{-
Note [Weak symbols]
~~~~~~~~~~~~~~~~~~~
Weak symbols are like global symbols, except that a weak symbol is allowed to
be overridden by a global symbol of the same name. Libraries like libc use weak
symbols all over the place. For instance, libc might have a weak symbol named
setuid and a global symbol named __setuid at the same function address. A PLT
stub that jumps to setuid() will likely use the former symbol name, however,
so it's important to make our ELF loader aware of them.

Much of the time, if a weak symbol exists in a binary, then there is no
corresponding global symbol of the same name. This is because the linker
usually removes weak symbols of this sort, so by the time the verifier
simulates the binary, any potential name conflicts between weak and global
symbols have already been resolved. Still, it's difficult to state with
confidence that such a scenario could never happen. Just in case it does,
we manually resolve such naming conflicts (in `addSymbolWithPriority`) by
favoring global symbols over weak symbols in case of a name conflict.
-}
