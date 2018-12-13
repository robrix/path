module Path.Name where

import Data.List.NonEmpty
import Data.Semilattice.Lower
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen

newtype Name = Name { getName :: String }
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty (Name s) = pretty s

instance PrettyPrec Name where
  prettyPrec _ = pretty

instance Lower Name where
  lowerBound = Name "_"


data ModuleName
  = ModuleName String
  | ModuleName :. String
  deriving (Eq, Ord, Show)

infixl 5 :.

instance Pretty ModuleName where
  pretty (ModuleName s) = pretty s
  pretty (ss :. s) = pretty ss <> dot <> pretty s

makeModuleName :: NonEmpty String -> ModuleName
makeModuleName (s:|ss) = foldl (:.) (ModuleName s) ss


type PackageName = String
