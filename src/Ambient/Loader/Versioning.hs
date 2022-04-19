{-# LANGUAGE DeriveTraversable #-}

module Ambient.Loader.Versioning
  ( VersionedSymbol(..)
  , VersionedFunctionName
  , eqVersionedSymbolStrict
  , compareVersionedSymbolStrict
  , takeSymbolVersionFileName
  ) where

import qualified Data.ByteString.Char8 as BSC
import           Data.Function ( on )
import qualified Prettyprinter as PP
import qualified System.FilePath as SF

import qualified Data.BinarySymbols as BinSym
import qualified What4.FunctionName as WF

-- | A symbol paired with version information.

-- This is very similar to VersionedSymbol in binary-symbols:Data.BinarySymbols,
-- except that this version is made more polymorphic to allow symbols besides
-- ByteStrings.
data VersionedSymbol sym = VerSym
  { versymSymbol :: !sym
  , versymVersion :: !BinSym.SymbolVersion
  } deriving (Foldable, Functor, Traversable, Show)

-- | Check for equality modulo the leading directories in a
-- 'BinSym.VersionedSymbol's file path. For an explanation of why we check for
-- equality this way, see the Haddocks for 'takeSymbolVersionFileName'.
instance Eq sym => Eq (VersionedSymbol sym) where
  VerSym sym1 ver1 == VerSym sym2 ver2 =
    (sym1 == sym2) && ((==) `on` takeSymbolVersionFileName) ver1 ver2

-- | Perform a comparison modulo the leading directories in a
-- 'BinSym.VersionedSymbol's file path. For an explanation of why we perform
-- comparisons this way, see the Haddocks for 'takeSymbolVersionFileName'.
instance Ord sym => Ord (VersionedSymbol sym) where
  compare (VerSym sym1 ver1) (VerSym sym2 ver2) =
    compare sym1 sym2 <> (compare `on` takeSymbolVersionFileName) ver1 ver2

-- This code is cargo-culted from binary-symbols
-- (https://github.com/GaloisInc/flexdis86/blob/9b899ed652c80dd22aa7dd9f6920d0d13a077bf6/binary-symbols/src/Data/BinarySymbols.hs#L67-L76),
-- which is licensed under the 3-Clause BSD license.
instance PP.Pretty sym => PP.Pretty (VersionedSymbol sym) where
  pretty (VerSym sym ver) =
    PP.pretty sym PP.<>
      case ver of
        BinSym.UnversionedSymbol -> mempty
        BinSym.ObjectDefaultSymbol    v -> PP.pretty "@@" PP.<> PP.pretty (BSC.unpack v)
        BinSym.ObjectNonDefaultSymbol v -> PP.pretty  "@" PP.<> PP.pretty (BSC.unpack v)
        BinSym.VersionedSymbol soName symName
          -> PP.pretty '@' PP.<> PP.pretty (BSC.unpack symName) PP.<>
             PP.pretty '(' PP.<> PP.pretty (BSC.unpack soName)  PP.<> PP.pretty ')'

-- | A versioned 'WF.FunctionName'. This is a common enough instantiation of
-- 'VersionedSymbol' that we define a specific alias for it.
type VersionedFunctionName = VersionedSymbol WF.FunctionName

-- | This behaves like the 'Eq' instance for 'VersionedSymbol', except that two
-- 'BinSym.VersionedSymbol's are considered distinct if they have different
-- leading directories in their file paths. (See the Haddocks for
-- 'takeSymbolVersionFileName' for more on this point.)
eqVersionedSymbolStrict :: Eq sym => VersionedSymbol sym -> VersionedSymbol sym -> Bool
eqVersionedSymbolStrict (VerSym sym1 ver1) (VerSym sym2 ver2) =
  (sym1 == sym2) && (ver1 == ver2)
infix 4 `eqVersionedSymbolStrict`

-- | This behaves like the 'Eq' instance for 'VersionedSymbol', except that two
-- 'BinSym.VersionedSymbol's are considered distinct if they have different
-- leading directories in their file paths. (See the Haddocks for
-- 'takeSymbolVersionFileName' for more on this point.)
compareVersionedSymbolStrict :: Ord sym => VersionedSymbol sym -> VersionedSymbol sym -> Ordering
compareVersionedSymbolStrict (VerSym sym1 ver1) (VerSym sym2 ver2) =
  compare sym1 sym2 <> compare ver1 ver2

-- | File paths in 'BinSym.VersionedSymbol's can contain directories. For
-- example, a main binary might require a symbol located in @foo/bar.so@. This
-- can pose challenges when checking 'BinSym.SymbolVersion's for equality,
-- since @foo/bar.so@'s symbol versions will likely contain @bar.so@ rather
-- than @foo/bar.so@.
--
-- To ensure that these symbol versions match up, this function can be used to
-- take everything in a 'BinSym.VersionedSymbol's file path except for the file
-- name, which is all that really matters for linking/loading purposes. It's a
-- bit heavy-handed, but it gets the job done.
takeSymbolVersionFileName :: BinSym.SymbolVersion -> BinSym.SymbolVersion
takeSymbolVersionFileName sv =
  case sv of
    BinSym.UnversionedSymbol{}      -> sv
    BinSym.ObjectDefaultSymbol{}    -> sv
    BinSym.ObjectNonDefaultSymbol{} -> sv
    BinSym.VersionedSymbol soName symName ->
      BinSym.VersionedSymbol (BSC.pack (SF.takeFileName (BSC.unpack soName))) symName
