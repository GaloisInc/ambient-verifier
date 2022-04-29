{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Ambient.Property.Definition (
    Transition(..)
  , State(..)
  , Property(..)
  , StateID
  , stateID
  , weirdMachineEntries
  , PropertyFinalStates(..)
  , propertyFinalStates
  -- * Parsing
  , parseProperty
  , PropertyParseError(..)
  ) where

import           Control.Applicative ( empty, (<|>) )
import           Control.Monad ( unless )
import qualified Control.Monad.Catch as CMC
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe )
import qualified Data.Set as Set
import           Data.String ( fromString )
import qualified Data.Text as T
import           Data.Void ( Void )
import           Data.Word ( Word64 )
import qualified Data.Yaml as DY
import qualified Text.Megaparsec as TM
import qualified Text.Megaparsec.Char as TMC
import qualified Text.Megaparsec.Char.Lexer as TMCL

import qualified What4.FunctionName as WF

import qualified Ambient.Panic as AP

newtype StateID = StateID { stateID :: Integer }
  deriving (Show, Eq, Ord)

type family StateName sid
type instance StateName () = T.Text
type instance StateName StateID = StateID

data Transition where
  -- | The program being verified enters the weird machine at the given address
  EnterWeirdMachine :: Word64 -> Transition
  -- | The program being verified issues the named system call
  IssuesSyscall :: T.Text -> Transition
  -- | The program being verifier invokes the named function. The function name
  -- is determined by @Ambient.Lift.discoveredFunName@, which chooses the
  -- function symbol name if it can find it and, failing that, falls back on
  -- the function address, formatted as @0xNNNNN...@. In the future, we may
  -- wish to make this event finer-grained.
  InvokesFunction :: WF.FunctionName -> Transition

deriving instance Show Transition

-- | The type of a state (final, semi-final, normal)
data StateType sid = NormalState
                   -- ^ A non-accept state
                   | FinalState
                   -- ^ An accept state; if there are any of these states, it is
                   -- required that the final state of the property trace be
                   -- entirely accepts
                   | SemiFinalState [StateName sid]
                   -- ^ A variant of the accept state that must be *possible*
                   -- given the final state, but where other non-final states
                   -- are also permitted.
                   --
                   -- If the list is empty, any other state is permitted
                   --
                   -- If the list is non-empty, the other states must be drawn
                   -- from that list

deriving instance (Eq (StateName sid)) => Eq (StateType sid)
deriving instance (Show (StateName sid)) => Show (StateType sid)

-- | States that can appear in the property language
data State sid =
  State { stateName :: T.Text
        -- ^ The name of the state
        , stateId :: sid
        -- ^ The unique identifier of the state
        , transitions :: [(Transition, StateName sid)]
        -- ^ Transitions from this state
        , stateType :: StateType sid
        -- ^ A marker to determine if the state is final (accept) or not
        , stateDescription :: Maybe T.Text
        -- ^ An optional user-provided description of the state
        }

deriving instance (Show sid, Show (StateName sid)) => Show (State sid)


-- | Properties that are to be checked by the verifier, expressed as state charts
--
-- Properties are polymorphic in the state id (@sid@). When they are initially
-- parsed, states do not have unique identifiers ('()'). After they are validated,
-- states have unique names and unique integer identifiers assigned to them ('StateID').
--
-- The unique integer identifiers correspond to the state IDs that will appear
-- in the symbolic event trace constructed by the verifier.
--
-- NOTE: When we extend the verifier to support multiple properties, we will
-- need a global index of state IDs, or a separate trace for each property (that
-- we probably want to carefully ensure remains tied only to the associated
-- property).
data Property sid =
  Property { propertyName :: T.Text
           , initialStateName :: T.Text
           , initialState :: StateName sid
           , states :: Map.Map (StateName sid) (State sid)
           , propertyDesscription :: Maybe T.Text
           -- ^ An optional user-provided description of the property
           }

deriving instance (Show (StateName sid), Show sid) => Show (Property sid)

-- | Collect all of the Weird Machine entry points in a 'Property'
weirdMachineEntries :: Property sid -> Set.Set Word64
weirdMachineEntries p =
  Set.fromList
    [ entry
    | st <- Map.elems (states p)
    , (t, _) <- transitions st
    , EnterWeirdMachine entry <- return t
    ]

-- | States that a trace must be in at the end of an execution
data PropertyFinalStates = AlwaysOneOf [StateID]
                         -- ^ All final states must be from this set
                         | PossiblyOneOfOr [(StateID, [StateID])]
                         -- ^ The final state must be able to be the first in
                         -- the pairs, and if it is, it may also be one of the
                         -- other non-final states
                         deriving (Show)

propertyFinalStates :: Property StateID -> PropertyFinalStates
propertyFinalStates p
  | hasAnyFinal =
    AlwaysOneOf [ stateId s
                | s <- Map.elems (states p)
                , FinalState <- return (stateType s)
                ]
  | otherwise =
    PossiblyOneOfOr [ (stateId s, sts)
                    | s <- Map.elems (states p)
                    , SemiFinalState sts <- return (stateType s)
                    ]
  where
    hasAnyFinal = any ((FinalState==) . stateType) (Map.elems (states p))

-- Parsing

data PropertyParseError = ExpectedObject DY.Value
                        | ExpectedObjectKey DY.Object String
                        | UnexpectedValueTypeAt DY.Object String
                        | EventParseError (TM.ParseErrorBundle T.Text Void)
                        | StateTypeParseError (TM.ParseErrorBundle T.Text Void)
                        | TransitionToInvalidState (Property ()) T.Text
                        | InvalidStartState (Property ())
                        | NonUniqueStateName [T.Text]
  deriving (Show)

instance CMC.Exception PropertyParseError

type Parser = TM.Parsec Void T.Text

-- | Attempt to interpret the given 'DY.Value' as an 'DY.Object', and return the
-- value at the named key
asObjectKey
  :: (CMC.MonadThrow m, DY.FromJSON a)
  => DY.Value
  -> String
  -> m a
asObjectKey val key =
  case val of
    DY.Object o ->
      case DY.parseMaybe (DY..:? fromString key) o of
        Nothing -> CMC.throwM (ExpectedObjectKey o key)
        Just Nothing -> CMC.throwM (UnexpectedValueTypeAt o key)
        Just (Just a) -> return a
    _ -> CMC.throwM (ExpectedObject val)

asObjectKeyMaybe
  :: (CMC.MonadThrow m, DY.FromJSON a)
  => DY.Value
  -> String
  -> m (Maybe a)
asObjectKeyMaybe val key =
  case val of
    DY.Object o ->
      case DY.parseMaybe (DY..:? fromString key) o of
        Nothing -> return Nothing
        Just Nothing -> return Nothing
        Just (Just a) -> return (Just a)
    _ -> CMC.throwM (ExpectedObject val)

-- | A standard space consumer that does not support comments
spaceConsumer :: Parser ()
spaceConsumer = TMCL.space TMC.space1 empty empty

symbol :: TM.Tokens T.Text -> Parser T.Text
symbol = TMCL.symbol spaceConsumer

identifier :: Parser T.Text
identifier = do
  c1 <- TMC.letterChar
  cs <- TM.many TMC.alphaNumChar
  return (T.pack (c1 : cs))

parens :: Parser a -> Parser a
parens = TM.between (symbol "(") (symbol ")")

parseEnterWM :: Parser Transition
parseEnterWM = do
  _ <- symbol "EnterWeirdMachine"
  addr <- parens (symbol "0x" >> TMCL.hexadecimal)
  return (EnterWeirdMachine addr)

parseIssuesSyscall :: Parser Transition
parseIssuesSyscall = do
  _ <- symbol "IssuesSyscall"
  name <- parens identifier
  return (IssuesSyscall name)

parseInvokesFunction :: Parser Transition
parseInvokesFunction = do
  _ <- symbol "InvokesFunction"
  name <- parens identifier
  pure $ InvokesFunction $ WF.functionNameFromText name

parseEventString :: Parser Transition
parseEventString = TM.try parseEnterWM
               <|> TM.try parseIssuesSyscall
               <|> parseInvokesFunction

parseEvent
  :: (CMC.MonadThrow m)
  => T.Text
  -> m Transition
parseEvent txt =
  case TM.runParser parseEventString "property" txt of
    Left err -> CMC.throwM (EventParseError err)
    Right t -> return t

parseTransition
  :: (CMC.MonadThrow m)
  => DY.Value
  -> m (Transition, T.Text)
parseTransition v0 = do
  target <- asObjectKey v0 "target"
  event <- asObjectKey v0 "event"

  evt <- parseEvent event

  return (evt, target)

stateIdentifier :: Parser T.Text
stateIdentifier = T.pack <$> TM.some TMC.alphaNumChar

parseStateType
  :: (CMC.MonadThrow m)
  => DY.Value
  -> m (StateType ())
parseStateType v0 = do
  mty <- asObjectKeyMaybe v0 "type"
  case mty of
    Nothing -> return NormalState
    Just ty ->
      case TM.runParser parseTypeString "state type" ty of
        Left err -> CMC.throwM (StateTypeParseError err)
        Right t -> return t
  where
    parseTypeString = TM.try (FinalState <$ symbol "final")
                  <|> (SemiFinalState <$> (symbol "semi-final" >> parens (TM.sepBy1 stateIdentifier (symbol ","))))

parseState
  :: (CMC.MonadThrow m)
  => DY.Value
  -> m (State ())
parseState v0 = do
  name <- asObjectKey v0 "name"
  ty <- parseStateType v0
  mdesc <- asObjectKeyMaybe v0 "description"

  -- There might not be any transitions specified (e.g., for a final state), so
  -- don't fail if the key doesn't exist
  transitionList <- asObjectKeyMaybe v0 "transitions"
  ts <- maybe (return []) (mapM parseTransition) transitionList

  return State { stateName = name
               , stateType = ty
               , transitions = ts
               , stateId = ()
               , stateDescription = mdesc
               }


-- | Traverse the property and validate that all of the transitions reference
-- states that exist in the property
validateProperty
  :: (CMC.MonadThrow m)
  => Property ()
  -> m (Property StateID)
validateProperty p = do
  let stateNamesList = fmap stateName (F.toList (states p))
  let stateNames = Set.fromList stateNamesList

  unless (Set.size stateNames == length stateNamesList) $ do
    CMC.throwM (NonUniqueStateName stateNamesList)

  F.forM_ (states p) $ \s -> do
    F.forM_ (transitions s) $ \(_, target) -> do
      unless (Set.member target stateNames) $ do
        CMC.throwM (TransitionToInvalidState p target)
  unless (Set.member (initialStateName p) stateNames) $ do
    CMC.throwM (InvalidStartState p)

  let stateNameIDs = Map.fromList (zip stateNamesList (map StateID [0..]))
  let assignStateID s0 = State { stateName = stateName s0
                               , stateId =
                                 let Just sid = Map.lookup (stateName s0) stateNameIDs
                                 in sid
                               , transitions = [ (t, sid)
                                               | (t, tname) <- transitions s0
                                               , let Just sid = Map.lookup tname stateNameIDs
                                               ]
                               , stateType = fixupStateTypeIdent stateNameIDs (stateType s0)
                               , stateDescription = stateDescription s0
                               }
  let assignStateIDs = Map.fromList [ (stateId st, st)
                                    | s0 <- Map.elems (states p)
                                    , let st = assignStateID s0
                                    ]
  case F.find ((initialStateName p ==) . stateName) assignStateIDs of
    Nothing -> CMC.throwM (InvalidStartState p)
    Just s0 -> do
      let p' = Property { propertyName = propertyName p
                        , initialStateName = initialStateName p
                        , initialState = stateId s0
                        , states = assignStateIDs
                        , propertyDesscription = propertyDesscription p
                        }
      return p'
  where
    lookupNameID m name = Map.lookup name m
    fixupStateTypeIdent m st0 =
      case st0 of
        NormalState -> NormalState
        FinalState -> FinalState
        SemiFinalState names ->
          let panic = AP.panic AP.PropertyParser "fixupStateTypeIdent" ["No identifier for component: " ++ show names]
          in SemiFinalState (map (fromMaybe panic . lookupNameID m) names)

-- | Parse a YAML value into a property (or return an error)
--
-- The YAML format is the one defined by the Sismic project: https://sismic.readthedocs.io/en/latest/format.html
--
-- There is an extension in that states may be semi-final. See the documentation
-- for 'StateType' for details.
parseProperty
  :: (CMC.MonadThrow m)
  => DY.Value
  -> m (Property StateID)
parseProperty v0 = do
  rootVal <- asObjectKey v0 "statechart"
  pname <- asObjectKey rootVal "name"
  rootState <- asObjectKey rootVal "root state"
  mdesc <- asObjectKeyMaybe rootVal "description"

  istateName <- asObjectKey rootState "initial"
  statesList <- asObjectKey rootState "states"

  parsedStates <- mapM parseState statesList

  let p = Property { propertyName = pname
                   , initialStateName = istateName
                   , initialState = istateName
                   , states = Map.fromList [ (stateName s, s) | s <- parsedStates ]
                   , propertyDesscription = mdesc
                   }

  validateProperty p
