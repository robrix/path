module Path.Name where

import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen

newtype Name = Local { getName :: String }
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty (Local s) = pretty s

instance PrettyPrec Name where
  prettyPrec _ = pretty
