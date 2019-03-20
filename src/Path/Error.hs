{-# LANGUAGE TypeOperators #-}
module Path.Error where

import Path.Context as Context
import Path.Name
import Path.Pretty
import Path.Usage
import Path.Value
import Text.Trifecta.Rendering (Span)

data ElabError = ElabError
  { errorSpan    :: Span
  , errorContext :: Context (Type Meta)
  , errorReason  :: ErrorReason
  }
  deriving (Eq, Ord, Show)

data ErrorReason
  = FreeVariable Name
  | ResourceMismatch Gensym Usage Usage [Span]
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (ElabError span ctx reason) = case reason of
    FreeVariable name -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) (prettyCtx ctx)
    ResourceMismatch n pi used uses -> prettyErr span msg (prettyCtx ctx <> map prettys uses)
      where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length uses)) <+> pretty "than required" <+> parens (pretty pi)
    where prettyCtx ctx = if null ctx then [] else [nest 2 (vsep [pretty "Local bindings:", pretty ctx])]

instance PrettyPrec ElabError
