module Ambient.Timeout (
  Timeout(..),
  Microseconds,
  defaultTimeout,
  timeoutAsMicros,
  microsAsInt
  ) where

-- | Specify a timeout.  Currently the timeout must be specified in seconds,
-- but additional Timeout constructors may be added in the future.
newtype Timeout = Seconds Int
  deriving (Eq, Ord, Show, Read)

newtype Microseconds = Microseconds Int
  deriving (Show, Read, Eq, Ord)

defaultTimeout :: Timeout
defaultTimeout = Seconds 30

-- | Convert a Timeout to a number of microseconds
timeoutAsMicros :: Timeout -> Microseconds
timeoutAsMicros (Seconds s) = Microseconds (s * 1000000)

-- | Convert a Microseconds to an Int
microsAsInt :: Microseconds -> Int
microsAsInt (Microseconds u) = u
