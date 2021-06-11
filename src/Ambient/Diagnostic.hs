{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Ambient.Diagnostic (
  Diagnostic(..)
  ) where

import qualified Prettyprinter as PP

data Diagnostic where

instance Show Diagnostic

instance PP.Pretty Diagnostic where
  pretty d =
    case d of
