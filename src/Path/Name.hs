module Path.Name where

import Text.PrettyPrint.ANSI.Leijen

data Name
  = Global String
  | Local String
  | Quote String
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty (Global s) = pretty s
  pretty (Local s) = pretty s
  pretty (Quote s) = pretty s
