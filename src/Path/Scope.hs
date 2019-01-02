module Path.Scope where

import qualified Data.Map as Map
import Path.Context
import Path.Name
import Path.Pretty
import Path.Value

data Entry
  = Decl Type
  | Defn (Typed Value)
  deriving (Eq, Ord, Show)

instance Pretty Entry where
  pretty (Decl        ty)  =                             colon <+> pretty ty
  pretty (Defn (v ::: ty)) = pretty "=" <+> pretty v <+> colon <+> pretty ty

instance PrettyPrec Entry


newtype Scope = Scope { unScope :: Map.Map QName Entry }
  deriving (Eq, Ord, Show)
