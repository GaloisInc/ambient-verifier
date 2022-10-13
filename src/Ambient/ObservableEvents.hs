{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Ambient.ObservableEvents (
    RecordObservableEvent(..)
  , ObservableEventConfig(..)
  , ObservableEvent(..)
  , ObservableEventTraceType
  , observableEventTraceRepr
  , buildRecordObservableEvent
  ) where

import qualified Data.Aeson as DA
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import qualified Data.Map.Strict as Map

import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.SymSequence as LCSS
import qualified Lang.Crucible.Types as LCT
import qualified What4.Interface as WI

import qualified Ambient.Panic as AP
import qualified Ambient.Property.Definition as APD

-- A function to record an observable event by consing it to a sequence of
-- events.
newtype RecordObservableEvent sym =
  RecordObservableEvent ( sym
                       -> APD.Transition
                       -- ^ Event to record
                       -> WI.Pred sym
                       -- ^ Path condition
                       -> LCSS.SymSequence sym (WI.SymInteger sym)
                       -- ^ Sequence to add event to.
                       -> IO (LCSS.SymSequence sym (WI.SymInteger sym)) )

-- | Configuration information for observable events recording
data ObservableEventConfig sym = ObservableEventConfig {
    oecGlobal :: LCS.GlobalVar ObservableEventTraceType
 -- ^ Global variable holding the observable event trace
  , oecRecordFn :: RecordObservableEvent sym
 -- ^ Function to record an observable event
  }

-- | An individual observable event
data ObservableEvent = ObservableEvent {
    oeEvent :: APD.Transition
 -- ^ The event itself
  , oeId :: Int
 -- ^ A unique ID for the event
  , oeParents :: [Int]
 -- ^ A list of parents in the event trace.  In most cases this will be a
 -- singleton, but an event may have multiple parents if it follows a merge
 -- node in the event sequence.  This list may also be empty if this event is
 -- at the start of the event trace and therefore has no parents.
  , oePathCondition :: String
 -- ^ Path condition for the event.
  } deriving (Show, Eq, Ord)

instance DA.ToJSON ObservableEvent where
  toJSON (ObservableEvent evt evtId parents pathCond) =
    DA.object $ [ "id" DA..= evtId
                , "parents" DA..= parents
                , "pathCondition" DA..= pathCond ]
             ++ typeSpecificFields
    where
      typeSpecificFields =
        case evt of
          APD.EnterWeirdMachine addr ->
            [ "type" DA..= ("enterWeirdMachine" :: String)
            , "address" DA..= addr
            ]
          APD.IssuesSyscall name ->
            [ "type" DA..= ("systemCall" :: String)
            , "name" DA..= name
            ]
          APD.InvokesFunction name ->
            [ "type" DA..= ("functionCall" :: String)
            , "name" DA..= show name
            ]

type ObservableEventTraceType = LCT.SequenceType LCT.IntegerType

observableEventTraceRepr :: LCT.TypeRepr ObservableEventTraceType
observableEventTraceRepr = LCT.SequenceRepr LCT.IntegerRepr

-- | Construct the necessary components for recording observable events.
-- Returns a reference to a mapping from event IDs to events, as well as a
-- 'RecordObservableEvent' function to build up the sequence of events.
buildRecordObservableEvent
  :: forall sym
   . WI.IsExprBuilder sym
  => IO ( IORef (Map.Map Int ObservableEvent), RecordObservableEvent sym )
buildRecordObservableEvent = do
  transitionIdsRef <- newIORef Map.empty
  let recordFn = \sym transition pathCond tSequence -> do
        transitionIds <- readIORef transitionIdsRef
        let tid = Map.size transitionIds
        let event = ObservableEvent transition
                                    tid
                                    (parents tSequence)
                                    (show (WI.printSymExpr pathCond))
        writeIORef transitionIdsRef (Map.insert tid event transitionIds)
        stid <- WI.intLit sym (fromIntegral tid)
        LCSS.consSymSequence sym stid tSequence
  return (transitionIdsRef, RecordObservableEvent recordFn)
  where
    -- Return the would-be parents of a node consed on to a given sequence.
    parents :: WI.IsExpr (WI.SymExpr sym)
            => LCSS.SymSequence sym (WI.SymInteger sym)
            -> [Int]
    parents sseq =
      case sseq of
        LCSS.SymSequenceNil -> []
        LCSS.SymSequenceCons _ h _ ->
          case WI.asInteger h of
            Just i -> [fromInteger i]
            Nothing ->
              -- This shouldn't be possible because we only insert concrete
              -- integers into the sequence.
              AP.panic AP.ObservableEvents
                       "buildRecordObservableEvent"
                       ["Encountered symbolic event ID"]
        LCSS.SymSequenceAppend _ l r ->
          case parents l of
            [] -> parents r
            lParents -> lParents
        LCSS.SymSequenceMerge _ _ l r ->
          parents l ++ parents r
