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
  = FreeVariable (Name Local)
  | IllegalApplication (Type Meta)
  | ResourceMismatch Gensym Usage Usage [Span]
  | TypedHole (Name Local) (Type Meta)
  | InfiniteType (Name Local) (Type Meta)
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (ElabError span ctx reason) = case reason of
    FreeVariable name -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) (prettyCtx ctx)
    IllegalApplication ty -> prettyErr span (pretty "illegal application of term of type" <+> pretty ty) (prettyCtx ctx)
    ResourceMismatch n pi used uses -> prettyErr span msg (prettyCtx ctx <> map prettys uses)
      where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length uses)) <+> pretty "than required" <+> parens (pretty pi)
    TypedHole n ty -> prettyErr span msg (prettyCtx ctx)
      where msg = pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
    InfiniteType n t -> prettyErr span (pretty "Cannot construct infinite type" <+> pretty n <+> blue (pretty "~") <+> pretty t) (prettyCtx ctx)
    where prettyCtx ctx = if null ctx then [] else [nest 2 (vsep [pretty "Local bindings:", pretty ctx])]

instance PrettyPrec ElabError
