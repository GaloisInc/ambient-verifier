{-# LANGUAGE TemplateHaskell #-}
module Ambient.Panic (
    panic
  , Component(..)
  ) where

import qualified Panic as P

data Component = Extensions
               | FunctionOverride
               | Memory
               | Loader
               | ObservableEvents
               | Override
               | Property
               | SymbolicExecution
               | Syscall
               | Verifier
               | WME
               | WMM
  deriving (Show)

instance P.PanicComponent Component where
  panicComponentName = show
  panicComponentIssues _ = "https://gitlab-ext.galois.com/ambient/verifier/-/issues"
  panicComponentRevision = $(P.useGitRevision)

panic :: Component -> String -> [String] -> a
panic = P.panic
