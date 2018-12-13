module Path.Name where

import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen

data Name
  = Local String
  | Quote String
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty (Local s) = pretty s
  pretty (Quote s) = pretty s

instance PrettyPrec Name where
  prettyPrec _ = pretty
