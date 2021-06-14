{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
-- | This module provides an interface for instantiating SMT solvers
--
-- The intent of this module is to make it easy to select a solver from the
-- command line (i.e., via a flag), while still introducing all of the complex
-- existentials necessary for introducing solver state types and typeclass
-- constraints.
module Ambient.Solver (
    Solver(..)
  , FloatMode(..)
  , withOnlineSolver
  ) where

import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( MonadIO )
import qualified Data.Parameterized.Nonce as PN
import qualified What4.Expr as WE
import qualified What4.ProblemFeatures as WP

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO

import qualified Ambient.Exception as AE

-- | The solver to use
--
-- This can be the solver used for online path satisfiability checking or for
-- discharging individual verification conditions
data Solver = Boolector
            | CVC4
            | Yices
            | Z3
            deriving (Read, Show, Eq, Ord)

-- | The interpretation of floating point operations
data FloatMode = IEEE
               -- ^ Use a bit-precise interpretation; this is the most faithful
               -- to the program semantics, but often yields queries that are unsolvable
               | Real
               -- ^ Approximate floating point operations as reals; this is
               -- scalable, but not entirely faithful to the machine
               -- semantics. In particular, it doesn't provide any way to reason
               -- about precision, NaN, or denormal values.
               | UF
               -- ^ Leave floating point operations uninterpreted
               --
               -- This can yield false positive models, and is usually only
               -- suitable for syntactic equivalence queries
               deriving (Read, Show, Eq, Ord)

-- | Run a continuation with the selected solver and floating point interpretation
--
-- This function provides an online solver suitable for path satisfiability
-- checking.
withOnlineSolver
  :: (MonadIO m, CMC.MonadMask m)
  => Solver
  -> FloatMode
  -> PN.NonceGenerator IO scope
  -> (forall sym solver fs . (sym ~ LCBO.OnlineBackend scope solver fs, LCB.IsSymInterface sym) => sym -> m a)
  -> m a
withOnlineSolver solver fm ng k =
  case solver of
    Boolector ->
      -- See Note [Float Mode Duplication]
      case fm of
        IEEE -> CMC.throwM (AE.UnsupportedSolverCombination (show solver) (show fm))
        Real -> CMC.throwM (AE.UnsupportedSolverCombination (show solver) (show fm))
        UF -> LCBO.withBoolectorOnlineBackend WE.FloatUninterpretedRepr ng LCBO.NoUnsatFeatures k
    CVC4 ->
      case fm of
        IEEE -> LCBO.withCVC4OnlineBackend WE.FloatIEEERepr ng LCBO.NoUnsatFeatures WP.noFeatures k
        Real -> LCBO.withCVC4OnlineBackend WE.FloatRealRepr ng LCBO.NoUnsatFeatures WP.noFeatures k
        UF -> LCBO.withCVC4OnlineBackend WE.FloatUninterpretedRepr ng LCBO.NoUnsatFeatures WP.noFeatures k
    Yices ->
      case fm of
        IEEE -> CMC.throwM (AE.UnsupportedSolverCombination (show solver) (show fm))
        Real -> LCBO.withYicesOnlineBackend WE.FloatRealRepr ng LCBO.NoUnsatFeatures WP.noFeatures k
        UF -> LCBO.withYicesOnlineBackend WE.FloatUninterpretedRepr ng LCBO.NoUnsatFeatures WP.noFeatures k
    Z3 ->
      case fm of
        IEEE -> LCBO.withZ3OnlineBackend WE.FloatIEEERepr ng LCBO.NoUnsatFeatures WP.noFeatures k
        Real -> LCBO.withZ3OnlineBackend WE.FloatRealRepr ng LCBO.NoUnsatFeatures WP.noFeatures k
        UF -> LCBO.withZ3OnlineBackend WE.FloatUninterpretedRepr ng LCBO.NoUnsatFeatures WP.noFeatures k

{- Note [Float Mode Duplication]

The duplication here is unfortunate, but we have to do it because there is no
good way to capture the floating point interface constraint without a literal
repr here. There doesn't seem to be a better way to do this because we need the
repr to instantiate the symbolic interface, but we can't get the appropriate
instance without having a symbolic interface. This duplication (and therefore
inlining of the reprs) breaks the cyclic dependency.

-}
