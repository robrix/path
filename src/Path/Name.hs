module Path.Name where

import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen

newtype Name = Name { getName :: String }
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty (Name s) = pretty s

instance PrettyPrec Name where
  prettyPrec _ = pretty
