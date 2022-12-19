{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Ambient.ObservableEvents (
    ObservableEventType(..)
  , RecordObservableEvent(..)
  , ObservableEventConfig(..)
  , ObservableEvent(..)
  , ObservableEventTraceType
  , observableEventTraceRepr
  , buildRecordObservableEvent
  ) where

import qualified Data.Aeson as DA
import qualified Data.BitVector.Sized as BVS
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import qualified Data.Map.Strict as Map
import           Numeric ( showHex )

import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.SymSequence as LCSS
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI

import qualified Ambient.Panic as AP
import qualified Ambient.Property.Definition as APD

-- | This datatype captures the possible types of observable events.  It is
-- effectively a subtype of 'APD.Transition', but with extra types to capture
-- events that we wish report as observable but not permit as state transitions
-- in our statecharts.
data ObservableEventType where
  Transition :: APD.Transition -> ObservableEventType

  -- 'AppliesFunctionOverride' is specifically for function overrides
  -- (not syscall overrides or overrides called within other overrides).  The
  -- motivation for this is:
  --   1. Syscalls are always overrides.
  --   2. Function overrides can elide system calls.  This is not
  --      meaningfully true of overrides called within other overrides (as the
  --      outermost override would capture that the syscall was elided).
  AppliesFunctionOverride :: forall sym
                           . WI.IsExpr (WI.SymExpr sym)
                          => WF.FunctionName
                          -- ^ Override's name
                          -> [LCLM.SomePointer sym]
                          -- ^ Override's arguments
                          -> Maybe (LCLM.SomePointer sym)
                          -- ^ Override's return value.  'Nothing' if the
                          -- override returns '()'.
                          -> ObservableEventType

-- A function to record an observable event by consing it to a sequence of
-- events.
newtype RecordObservableEvent sym =
  RecordObservableEvent ( sym
                       -> ObservableEventType
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
    oeEvent :: ObservableEventType
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
  }

-- NOTE: The Eq and Ord instances for 'ObservableEvent' compare only the unique
-- IDs of the events.  This is necessary because it isn't clear how to specify
-- equality and comparison of the potentially symbolic values within
-- 'ObservableEventType'.  Because IDs are unique and there should be only one
-- sequence of events, it's OK to use only the event ID for these instances.
instance Eq ObservableEvent where
  x == y = oeId x == oeId y
instance Ord ObservableEvent where
  compare x y = compare (oeId x) (oeId y)

instance DA.ToJSON ObservableEvent where
  toJSON (ObservableEvent evt evtId parents pathCond) =
    DA.object $ [ "id" DA..= evtId
                , "parents" DA..= parents
                , "pathCondition" DA..= pathCond ]
             ++ typeSpecificFields
    where
      typeSpecificFields =
        case evt of
          Transition t ->
            case t of
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
          AppliesFunctionOverride name args mResult ->
            [ "type" DA..= ("functionOverrideApplication" :: String)
            , "name" DA..= show name
            , "knownArguments" DA..= map renderPtr args
            ]
            ++
            case mResult of
              Nothing -> []
              Just result -> [ "result" DA..= renderPtr result ]

      renderPtr p =
        case deconstructPointer p of
          Nothing -> DA.toJSON ("<symbolic>" :: String)
          Just (base, offset) ->
           if base == 0
           then DA.toJSON $ "0x" ++ showHex offset ""
           else DA.toJSON $ show base ++ "+0x" ++ showHex offset ""

      -- | Deconstruct a pointer into its component parts.  Returns 'Nothing' if
      -- one or both parts are symbolic.
      deconstructPointer :: WI.IsExpr (WI.SymExpr sym)
                         => LCLM.SomePointer sym
                         -> Maybe (Integer, Integer)
      deconstructPointer (LCLM.SomePointer (LCLM.LLVMPointer base off)) = do
        base' <- WI.asNat base
        off' <- WI.asBV off
        return (toInteger base', BVS.asUnsigned off')

type ObservableEventTraceType = LCT.SequenceType LCT.IntegerType

observableEventTraceRepr :: LCT.TypeRepr ObservableEventTraceType
observableEventTraceRepr = LCT.SequenceRepr LCT.IntegerRepr

-- | Construct the necessary components for recording observable events.
-- Returns a reference to a mapping from event IDs to events, as well as a
-- 'RecordObservableEvent' function to build up the sequence of events.
buildRecordObservableEvent
  :: forall sym
   . WI.IsExprBuilder sym
  => IO ( IORef (Map.Map Int ObservableEvent)
        , RecordObservableEvent sym )
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
