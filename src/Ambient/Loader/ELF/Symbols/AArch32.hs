{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Ambient.Loader.ELF.Symbols.AArch32 ( elfAarch32UnsupportedRels ) where

import qualified Control.Exception as X
import           Control.Monad ( unless )
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe, listToMaybe )
import           Data.Word ( Word64 )

import qualified Data.ElfEdit as DE
import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.LoadCommon as DMML

import qualified Ambient.Exception as AE
import qualified Ambient.Panic as AP

-- | Read the .rel.dyn sections from a collection of binaries and return a
-- mapping from unsupported relocation variable addresses to names of the
-- unsupported relocation types.
elfAarch32UnsupportedRels :: forall arch w f
                           . ( Integral (DE.ElfWordType w)
                             , DMM.MemWidth w
                             , Foldable f )
                          => f (DMB.LoadedBinary arch (DE.ElfHeaderInfo w))
                          -> IO (Map.Map (DMM.MemWord w) String)
elfAarch32UnsupportedRels = F.foldlM go Map.empty
  where
    go :: Map.Map (DMM.MemWord w) String
       -> DMB.LoadedBinary arch (DE.ElfHeaderInfo w)
       -> IO (Map.Map (DMM.MemWord w) String)
    go acc lb = do
      let elfHeaderInfo = DMB.originalBinary lb
      let (_, elf) = DE.getElf elfHeaderInfo

      -- NOTE: We don't currently support aarch32 binaries with .rela.dyn
      -- sections (see ticket #98)
      unless (null (DE.findSectionByName (BSC.pack ".rela.dyn") elf))
        (X.throw AE.Aarch32RelaDynUnsupported)

      return $ fromMaybe acc $ do
        relDyn <- listToMaybe $ DE.findSectionByName (BSC.pack ".rel.dyn") elf
        let relDynBytes = DE.elfSectionData relDyn
        rels <- rightToMaybe $ DE.decodeRelEntries (DE.elfData elf) relDynBytes
        let offset = fromMaybe 0 $ DMML.loadOffset $ DMB.loadOptions lb
        pure $ F.foldl' (updateMap offset) acc rels

    -- | Check whether a relocation is supported and update 'unsupported' if it
    -- is not.
    updateMap :: Word64
              -> Map.Map (DMM.MemWord w) String
              -> DE.RelEntry DE.ARM32_RelocationType
              -> Map.Map (DMM.MemWord w) String
    updateMap offset unsupported rel =
      let addr = DMM.memWord (fromIntegral offset + fromIntegral (DE.relAddr rel)) in
      if is_rel_type_supported rel
      -- In each of these updates we panic if a global already exists at the
      -- address.  This should not be possible and indicates that binaries are
      -- loaded at overlapping addresses.
      then unsupported
      else Map.insertWithKey panicAddrCollision
                             addr
                             (show (DE.relType rel))
                             unsupported

    panicAddrCollision addr _ _ =
      AP.panic AP.Loader
               "elfAarch32UnsupportedRels"
               ["Encoutered multiple globals at address: " ++ (show addr)]

    is_rel_type_supported rel =
      case DE.relType rel of
        DE.R_ARM_GLOB_DAT -> True
        _ -> False

    rightToMaybe :: Either l r -> Maybe r
    rightToMaybe = either (const Nothing) Just

