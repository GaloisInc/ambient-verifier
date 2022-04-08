{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | Various utilities for looking up function symbols in ELF binaries.
module Ambient.Loader.ELF.FunctionSymbols
  ( elfDynamicFuncSymbolMap
  , elfEntryPointAddrMap
  , elfEntryPointSymbolMap
  ) where

import qualified Control.Exception as X
import           Control.Monad ( guard )
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as DE
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe )
import qualified Data.Text.Encoding as DTE
import qualified Data.Text.Encoding.Error as DTEE
import qualified Data.Vector as DV
import           Data.Word ( Word32 )

import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.BinaryLoader.ELF as DMBE
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.LoadCommon as DMML
import qualified What4.FunctionName as WF

import qualified Ambient.Exception as AE
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
  Map.Map WF.FunctionName (DMM.MemWord w)
elfDynamicFuncSymbolMap = F.foldl' addFuncs Map.empty
  where
    addFuncs ::
      Map.Map WF.FunctionName (DMM.MemWord w) ->
      DMB.LoadedBinary arch (DE.ElfHeaderInfo w) ->
      Map.Map WF.FunctionName (DMM.MemWord w)
    addFuncs m loadedBinary =
      Map.unionWithKey
        (\nm addr1 addr2 -> X.throw $ AE.DynamicFunctionNameClash nm addr1 addr2)
        m (Map.fromList binaryMap)
      where
        elfHeaderInfo = DMB.originalBinary loadedBinary
        elfHeader = DE.header elfHeaderInfo
        elfBytes = DE.headerFileContents elfHeaderInfo
        elfShdrs = DE.headerShdrs elfHeaderInfo
        offset = fromMaybe 0 $ DMML.loadOffset $ DMB.loadOptions loadedBinary

        dynSymbolTable = concatMap DV.toList $ elfDynamicSymbolTable elfHeader elfBytes elfShdrs
        binaryMap = DE.elfClassInstances (DE.headerClass (DE.header elfHeaderInfo)) $
                    [ ( WF.functionNameFromText $ DTE.decodeUtf8With DTEE.lenientDecode $ DE.steName ste
                      , fromIntegral (DE.steValue ste) + fromIntegral offset
                      )
                    | ste <- dynSymbolTable
                    , isFuncSymbol ste
                    ]

-- | Return true if this symbol table entry appears corresponds to a
-- globally defined function.
--
-- Taken from reopt (https://github.com/GaloisInc/reopt), which is licensed
-- under the 3-Clause BSD license.
isFuncSymbol :: DE.SymtabEntry nm w -> Bool
isFuncSymbol e
  =  DE.steType  e == DE.STT_FUNC
  && DE.steBind  e == DE.STB_GLOBAL
  && DE.steIndex e /= DE.SHN_UNDEF
  && DE.steIndex e <  DE.SHN_LORESERVE

-- | Given a binary, map the resolved address offset of each entry point
-- function to its name. This includes entry points in both the static and
-- dynamic symbol tables.
elfEntryPointAddrMap ::
  (w ~ DMC.ArchAddrWidth arch, DMM.MemWidth w) =>
  DMB.LoadedBinary arch (DE.ElfHeaderInfo w) ->
  Map.Map (DMM.MemSegmentOff w) WF.FunctionName
elfEntryPointAddrMap loadedBinary =
  DE.elfClassInstances (DE.headerClass (DE.header elfHeaderInfo)) $
  Map.fromList [ ( case DMBE.resolveAbsoluteAddress mem addr of
                     Just addrOff -> addrOff
                     Nothing -> AP.panic AP.Loader "elfEntryPointAddrMap"
                                  ["Failed to resolve function address: " ++ show addr]
                 , WF.functionNameFromText $ DTE.decodeUtf8With DTEE.lenientDecode $ DE.steName ste
                 )
               | ste <- elfEntryPoints elfHeaderInfo
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
    [ ( WF.functionNameFromText $ DTE.decodeUtf8With DTEE.lenientDecode $ DE.steName ste
      , fromIntegral (DE.steValue ste) + fromIntegral offset
      )
    | ste <- elfEntryPoints elfHeaderInfo
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
  [DE.SymtabEntry BS.ByteString (DE.ElfWordType w)]
elfEntryPoints elfHeaderInfo =
  filter (\ste -> DE.steType ste == DE.STT_FUNC
               -- Somewhat surprisingly, there can be STT_FUNC entries whose
               -- values are zero. See, for instance, the static symbol table in
               -- tests/binaries/aarch32/main-args.exe. These won't resolve
               -- properly, so filter them out.
               && toInteger (DE.steValue ste) /= 0)
         (staticSymbolTable ++ dynSymbolTable)
  where
    elfHeader = DE.header elfHeaderInfo
    elfBytes = DE.headerFileContents elfHeaderInfo
    elfShdrs = DE.headerShdrs elfHeaderInfo

    staticSymbolTable = concatMap (either (error . show) (DV.toList . DE.symtabEntries))
                                  (DE.decodeHeaderSymtab elfHeaderInfo)
    dynSymbolTable = concatMap DV.toList $ elfDynamicSymbolTable elfHeader elfBytes elfShdrs

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
elfDynamicSymbolTable hdr contents shdrs = DE.elfClassInstances (DE.headerClass hdr) $ do
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
