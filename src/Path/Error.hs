{-# LANGUAGE LambdaCase #-}
module Path.Error where

import Data.Maybe (listToMaybe)
import Path.Context
import Path.Name
import Path.Pretty
import Path.Usage
import Text.Trifecta.Rendering (Span)

data ElabError
  = FreeVariable QName Span
  | TypeMismatch (Type QName) (Type QName) Span
  | NoRuleToInfer Context Span
  | IllegalApplication (Type QName) Span
  | ResourceMismatch Name Usage Usage Span [Span]
  | TypedHole QName (Type QName) Context Span
  | InfiniteType QName (Type QName) Span
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty = \case
    FreeVariable name span -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) Nothing
    TypeMismatch expected actual span -> prettyErr span (vsep
      [ pretty "type mismatch"
      , pretty "expected:" <+> pretty expected
      , pretty "  actual:" <+> pretty actual
      ]) Nothing
    NoRuleToInfer ctx span -> prettyErr span (pretty "no rule to infer type of term") (Just (prettyCtx ctx))
    IllegalApplication ty span -> prettyErr span (pretty "illegal application of term of type" <+> pretty ty) Nothing
    ResourceMismatch n pi used span spans -> prettyErr span msg (vsep (map prettys spans) <$ listToMaybe spans)
      where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length spans)) <+> pretty "than required" <+> parens (pretty pi)
    TypedHole n ty ctx span -> prettyErr span msg (Just (prettyCtx ctx))
      where msg = pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
    InfiniteType n t span -> prettyErr span (pretty "Cannot construct infinite type" <+> pretty n <+> blue (pretty "~") <+> pretty t) Nothing
    where prettyCtx ctx = nest 2 $ vsep
            [ pretty "Local bindings:"
            , pretty ctx
            ]

instance PrettyPrec ElabError
