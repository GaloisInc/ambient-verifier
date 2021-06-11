{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Ambient.Diagnostic (
  Diagnostic(..)
  ) where

import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map as Map
import qualified Prettyprinter as PP

import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM

data Diagnostic where
  -- | Report an event from the code discovery phase
  --
  -- Note: We may want to enhance this with an indicator of the module being loaded (e.g., a filename)
  DiscoveryEvent :: (DMM.MemWidth w) => DMD.AddrSymMap w -> DMD.DiscoveryEvent w -> Diagnostic

ppSymbol :: (DMM.MemWidth w) => Maybe BSC.ByteString -> DMM.MemSegmentOff w -> String
ppSymbol (Just fnName) addr = show addr ++ " (" ++ BSC.unpack fnName ++ ")"
ppSymbol Nothing addr = show addr

instance PP.Pretty Diagnostic where
  pretty d =
    case d of
      DiscoveryEvent symMap de ->
        case de of
          DMD.ReportAnalyzeFunction memOff ->
            PP.pretty "Starting to analyze a function at address " <> PP.pretty memOff
          DMD.ReportAnalyzeFunctionDone memOff ->
            PP.pretty "Finished analyzing a function at address " <> PP.pretty memOff
          DMD.ReportIdentifyFunction _ tgt rsn ->
            PP.hcat [ PP.pretty "Identified a candidate function entry point for function "
                    , PP.pretty (ppSymbol (Map.lookup tgt symMap) tgt)
                    , PP.pretty " because "
                    , PP.pretty (DMD.ppFunReason rsn)
                    ]
          DMD.ReportAnalyzeBlock _ baddr ->
            PP.pretty "Analyzing a block at address " <> PP.pretty baddr
