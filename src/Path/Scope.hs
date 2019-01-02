module Path.Scope where

import Path.Context
import Path.Pretty
import Path.Value

data Entry
  = Decl Type
  | Defn (Typed Value)

instance Pretty Entry where
  pretty (Decl        ty)  =                             colon <+> pretty ty
  pretty (Defn (v ::: ty)) = pretty "=" <+> pretty v <+> colon <+> pretty ty

instance PrettyPrec Entry
