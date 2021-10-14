module Ambient.EventTrace (
    EventTraceType
  , eventTraceRepr
  , recordEvent
  , invalidTransitionState
  , partialSequenceErrorState
  , sequenceAccessErrorState
  , Properties(..)
  ) where

import           Control.Lens ( (^.) )
import qualified Data.Foldable as F
import qualified What4.Interface as WI
import qualified What4.Partial as WP

import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.SymSequence as LCSS
import qualified Lang.Crucible.Types as LCT

import qualified Ambient.Property.Definition as APD

type EventTraceType = LCT.SequenceType LCT.IntegerType

eventTraceRepr :: LCT.TypeRepr EventTraceType
eventTraceRepr = LCT.SequenceRepr LCT.IntegerRepr

data Properties =
  Properties { properties :: [(APD.Property APD.StateID, LCS.GlobalVar EventTraceType)]
             }

invalidTransitionState :: Integer
invalidTransitionState = -1

partialSequenceErrorState :: Integer
partialSequenceErrorState = -2

sequenceAccessErrorState :: Integer
sequenceAccessErrorState = -3

-- | Record an entry in the event trace that indicates that we have entered any
-- states indicated by the provided predicate.
--
-- NOTE that this function does not modify the trace if there are no valid
-- transitions involving this event.
--
-- This function does not concretely inspect the event trace. Instead, it
-- symbolically pulls off the first element and constructs the next state out of
-- a mux tree over all possible (symbolic) transitions from this state. The next
-- state is consed onto the head of the sequence.
--
-- For example, this function could be supplied with a predicate that selected
-- all of the transitions into Weird Machines (i.e., 'APD.EnterWeirdMachine').
-- In that case, let the current state be @curState@. Assume that there is a
-- valid transition from @s1@ to @s2@ by a 'APD.EnterWeirdMachine' edge. The
-- next state is then:
--
-- > ite (curState == s1) s2 invalidTransitionState
recordEvent
  :: (WI.IsExprBuilder sym)
  => (APD.Transition -> Bool)
  -- ^ A predicate that returns True for the transitions that this event matches
  -> sym
  -- ^ The symbolic backend
  -> APD.Property APD.StateID
  -- ^ The property being verified
  -> LCSS.SymSequence sym (WI.SymInteger sym)
  -- ^ The current symbolic event trace
  -> IO (LCSS.SymSequence sym (WI.SymInteger sym))
recordEvent matchTransition sym prop evtTrace
  | null matchingTransitions = return evtTrace
  | otherwise = do
      phd <- LCSS.headSymSequence sym (WI.intIte sym) evtTrace
      case phd of
        WP.Err _ -> do
          -- This probably shouldn't be possible, but it won't hurt to have it here
          --
          -- We'll use this distinguished value to flag this type of error and
          -- distinguish it from natural errors due to a missing transition.
          --
          -- TODO: Emit a diagnostic here
          errState <- WI.intLit sym sequenceAccessErrorState
          LCSS.consSymSequence sym errState evtTrace
        WP.NoErr partial -> do
          -- In this case, the value *should* always be total. It should only be
          -- partial if the sequence was empty on at least one branch, but that
          -- cannot be (we start it non-empty and never remove elements). We could
          -- assert it here, but that doesn't seem like it would help us at all.
          --
          -- Instead, just always wrap it in a mux that returns this distinguished
          -- value if we get a partial result.
          --
          -- TODO: Likewise, emit a diagnostic when this happens
          errState <- WI.intLit sym partialSequenceErrorState

          let curState = partial ^. WP.partialValue
          invalidState <- WI.intLit sym invalidTransitionState

          -- If we don't have a catastrophic error, build a mux tree encoding the
          -- allowable transitions.  Basically:
          --
          -- > if curState == src1 then dst1
          -- > else if curState == src2 then dst2
          -- > ...
          -- > else -1
          --
          -- Where -1 is an invalid state transition
          let addTransition acc (src, dst) = do
                srcInt <- WI.intLit sym (APD.stateID src)
                dstInt <- WI.intLit sym (APD.stateID dst)
                eq <- WI.intEq sym curState srcInt
                WI.intIte sym eq dstInt acc
          symValidNextState <- F.foldlM addTransition invalidState matchingTransitions
          nextState <- WI.intIte sym (partial ^. WP.partialPred) symValidNextState errState
          LCSS.consSymSequence sym nextState evtTrace
  where
    matchingTransitions = [ (APD.stateId s, dst)
                          | s <- F.toList (APD.states prop)
                          , (t, dst) <- APD.transitions s
                          , matchTransition t
                          ]
