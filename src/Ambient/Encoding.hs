module Ambient.Encoding
  ( encodeCLIString
  , encodeCLIText
  , encodeCommandLineArguments
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as BSUtf8
import qualified Data.Text as DT
import qualified Data.Text.Encoding as DTE

-- | Encode a string taken from the command line argument to a 'BS.ByteString'.
-- Currently, this always uses UTF8 encoding. See @Note [Argument Encoding]@.
encodeCLIString :: String -> BS.ByteString
encodeCLIString = BSUtf8.fromString

-- | Encode text taken from the command line argument to a 'BS.ByteString'.
-- Currently, this always uses UTF8 encoding. See @Note [Argument Encoding]@.
encodeCLIText :: DT.Text -> BS.ByteString
encodeCLIText = DTE.encodeUtf8

-- | Encode textual command-line arguments to 'BS.ByteString's. Currently,
-- this always uses UTF8 encoding. See @Note [Argument Encoding]@.
encodeCommandLineArguments ::
  FilePath ->
  Maybe DT.Text ->
  [DT.Text] ->
  [BS.ByteString]
encodeCommandLineArguments binaryPath mbArgv0 argvRest =
  let argv0' = maybe (encodeCLIString binaryPath) encodeCLIText mbArgv0
      argvRest' = map encodeCLIText argvRest
  in argv0':argvRest'

{-
Note [Argument Encoding]
~~~~~~~~~~~~~~~~~~~~~~~~
Note that we are unconditionally encoding arguments from Text to UTF8. This
works for Linux and MacOS, but will not work for Windows, which will expect
UTF16LE (or perhaps UCS-2).
-}
