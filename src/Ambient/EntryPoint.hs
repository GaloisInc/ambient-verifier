{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}

module Ambient.EntryPoint
  ( EntryPoint(..)
  , entryPointAddrMaybe
  , resolveEntryPointAddrOff
  ) where

import qualified Control.Monad.Catch as CMC
import Data.Text ( Text )
import Data.Word ( Word64 )

import qualified Data.Macaw.BinaryLoader as DMB
import qualified Data.Macaw.BinaryLoader.ELF as DMBE
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM

import qualified Ambient.Exception as AE

-- | Where to begin simulation.
data EntryPoint addr
  = DefaultEntryPoint
    -- ^ Begin simulation at the default entry point. For now, this is the
    -- main() function. See @Note [Entry Point]@ for why.
  | EntryPointName Text
    -- ^ Begin simulation at the function with the given name.
  | EntryPointAddr addr
    -- ^ Begin simulation at the function with the given address.
  deriving (Foldable, Functor, Show, Traversable)

-- | Return @'Just' addr@ if the 'EntryPoint' is specified as an address.
-- Return 'Nothing' otherwise.
entryPointAddrMaybe :: EntryPoint addr -> Maybe addr
entryPointAddrMaybe (EntryPointAddr addr) = Just addr
entryPointAddrMaybe DefaultEntryPoint     = Nothing
entryPointAddrMaybe EntryPointName{}      = Nothing

-- | If an 'EntryPoint' consists of an address, attempt to resolve the address
-- as a 'DMM.MemSegmentOff', throwing an exception if the offset cannot be
-- determined. All other forms of 'EntryPoints' are returned unchanged.
resolveEntryPointAddrOff ::
  (CMC.MonadThrow m, DMM.MemWidth (DMC.ArchAddrWidth arch)) =>
  DMB.LoadedBinary arch binFmt ->
  EntryPoint Word64 ->
  m (EntryPoint (DMC.ArchSegmentOff arch))
resolveEntryPointAddrOff loadedBinary = traverse $ \addr ->
  let memAddr = DMM.memWord addr in
  case DMBE.resolveAbsoluteAddress (DMB.memoryImage loadedBinary) memAddr of
    Just seg -> pure seg
    Nothing -> CMC.throwM $ AE.EntryPointAddrOffResolutionFailure memAddr
