{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | Functionality for resolving symbolic expressions as concrete.
--
-- Much of this code is copied from PATE (https://github.com/GaloisInc/pate),
-- which is licensed under the 3-Clause BSD license.
module Ambient.Verifier.Concretize
  ( Concretize
  , concreteInteger
  , resolveSingletonSymbolicAs
  , resolveSingletonPointer
  ) where

import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Traversable as T
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified What4.BaseTypes as WT
import qualified What4.Expr as WE
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat
import qualified What4.Utils.BVDomain as WUB
import qualified What4.Utils.ResolveBounds.BV as WURB

import qualified Ambient.Panic as AP

data Concretize sym tp where
  Concretize :: (Show (WEG.GroundValue tp))
             => WT.BaseTypeRepr tp
             -> (WI.SymExpr sym tp -> Maybe (WEG.GroundValue tp)) -- Convert a symbolic term to a concrete value
             -> (sym -> WI.SymExpr sym tp -> WEG.GroundValue tp -> IO (WI.SymExpr sym WT.BaseBoolType)) -- Create a blocking clause from a concrete value
             -> (sym -> WEG.GroundValue tp -> IO (WI.SymExpr sym tp)) -- Create a symbolic term wrapping the concrete result
             -> Concretize sym tp

concreteInteger :: (LCB.IsSymInterface sym) => Concretize sym WI.BaseIntegerType
concreteInteger = Concretize WT.BaseIntegerRepr WI.asInteger toBlocking injectSymbolic
  where
    toBlocking sym symVal gv = WI.notPred sym =<< WI.intEq sym symVal =<< WI.intLit sym gv
    injectSymbolic = WI.intLit

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using the SMT solver
--
-- This asks for a model. If it gets one, it adds a blocking clause and asks for
-- another. If there was only one model, concretize the initial value and return
-- it. Otherwise, return the original symbolic value
resolveSingletonSymbolicAs
  :: ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , HasCallStack
     )
  => Concretize sym tp
  -- ^ The strategy for concretizing the type
  -> LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> WI.SymExpr sym tp
  -- ^ The symbolic term to concretize
  -> IO (WI.SymExpr sym tp)
resolveSingletonSymbolicAs (Concretize _tp asConcrete toBlocking injectSymbolic) bak val =
  let sym = LCB.backendGetSym bak in
  case asConcrete val of
    Just _ -> return val
    Nothing -> do
      LCBO.withSolverProcess bak (onlinePanic "resolveSingletonSymbolicValue") $ \sp -> do
        val' <- WPO.inNewFrame sp $ do
          msat <- WPO.checkAndGetModel sp "Concretize value (with no assumptions)"
          mmodel <- case msat of
            WSat.Unknown -> return Nothing
            WSat.Unsat {} -> return Nothing
            WSat.Sat mdl -> return (Just mdl)
          T.forM mmodel $ \mdl -> WEG.groundEval mdl val
        case val' of
          Nothing -> return val -- We failed to get a model... leave it symbolic
          Just concVal -> do
            WPO.inNewFrame sp $ do
              block <- toBlocking sym val concVal
              WPS.assume (WPO.solverConn sp) block
              msat <- WPO.checkAndGetModel sp "Concretize value (with blocking clause)"
              case msat of
                WSat.Unknown -> return val -- Total failure
                WSat.Sat _mdl -> return val  -- There are multiple models
                WSat.Unsat {} -> injectSymbolic sym concVal -- There is a single concrete result

onlinePanic :: String -> a
onlinePanic fnName = AP.panic AP.Verifier fnName ["Online solver support is not enabled"]

-- | Resolve a 'WI.SymNat' to concrete, if possible.
resolveSymNat ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , HasCallStack
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> WI.SymNat sym
  -- ^ The symbolic natural number to concretize
  -> IO (WI.SymNat sym)
resolveSymNat bak symNat = do
  let sym = LCB.backendGetSym bak
  symInt <- WI.natToInteger sym symNat
  resolvedSymInt <- resolveSingletonSymbolicAs concreteInteger bak symInt
  WI.integerToNat sym resolvedSymInt

-- | Resolve a 'WI.SymBV' to concrete, if possible. If the 'WI.SymBV' is truly
-- symbolic, this will try to constrain the lower and uppper bounds as much as
-- possible.
resolveSymBV ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , 1 <= w
     , HasCallStack
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> PN.NatRepr w
  -- ^ The bitvector width
  -> WI.SymBV sym w
  -- ^ The symbolic bitvector to concretize
  -> IO (WI.SymBV sym w)
resolveSymBV bak w symBV =
  LCBO.withSolverProcess bak (onlinePanic "resolveSymBV") $ \sp -> do
    let sym = LCB.backendGetSym bak
    resBV <- WURB.resolveSymBV sym WURB.ExponentialSearch w sp symBV
    case resBV of
      WURB.BVConcrete bv -> WI.bvLit sym w bv
      WURB.BVSymbolic d  -> do
        -- NB: Use annotateTerm here to ensure that subsequent What4
        -- simplifications do not rearrange the underlying expression, which
        -- could potentially widen the bounds. There is a chance that not
        -- simplifying the underlying expression could inhibit some potential
        -- optimizations, but we err on the side of having narrower bounds,
        -- which is generally more beneficial for the crucible-llvm memory
        -- model.
        (_, symBV') <- WI.annotateTerm sym $
                       WI.unsafeSetAbstractValue (WUB.BVDArith d) symBV
        pure symBV'

-- | Resolve an 'LCLM.LLVMPtr' to concrete, if possible
--
-- The block id and offset are concretized independently, and either (or
-- neither) could be updated
resolveSingletonPointer
  :: ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , 1 <= w
     , HasCallStack
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> LCLM.LLVMPtr sym w
  -- ^ The symbolic term to concretize
  -> IO (LCLM.LLVMPtr sym w)
resolveSingletonPointer bak (LCLM.LLVMPointer base off) = do
  base' <- resolveSymNat bak base
  off' <- resolveSymBV bak (WI.bvWidth off) off
  return (LCLM.LLVMPointer base' off')
