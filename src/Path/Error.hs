module Path.Error where

import Data.Foldable (fold)
import Data.List.NonEmpty (NonEmpty(..))
import Path.Constraint
import Path.Context as Context
import Path.Name
import Path.Pretty
import Path.Usage
import Path.Value
import Text.Trifecta.Rendering (Span)

data ElabError = ElabError
  { errorSpan    :: NonEmpty Span
  , errorContext :: Context
  , errorReason  :: ErrorReason
  }
  deriving (Eq, Ord, Show)

data ErrorReason
  = FreeVariable QName
  | TypeMismatch (Equation Value)
  | NoRuleToInfer
  | IllegalApplication Type
  | ResourceMismatch Name Usage Usage
  | TypedHole QName Type
  | InfiniteType QName Type
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (ElabError spans ctx reason) = case reason of
    FreeVariable name -> prettyErr spans (pretty "free variable" <+> squotes (pretty name)) (prettyCtx ctx)
    TypeMismatch (expected :===: actual) -> prettyErr spans (fold (punctuate hardline
      [ pretty "type mismatch"
      , pretty "expected:" <+> pretty expected
      , pretty "  actual:" <+> pretty actual
      ])) (prettyCtx ctx)
    NoRuleToInfer -> prettyErr spans (pretty "no rule to infer type of term") (prettyCtx ctx)
    IllegalApplication ty -> prettyErr spans (pretty "illegal application of term of type" <+> pretty ty) (prettyCtx ctx)
    ResourceMismatch n pi used -> prettyErr spans msg (prettyCtx ctx)
      where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length spans)) <+> pretty "than required" <+> parens (pretty pi)
    TypedHole n ty -> prettyErr spans msg (prettyCtx ctx)
      where msg = pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
    InfiniteType n t -> prettyErr spans (pretty "Cannot construct infinite type" <+> pretty n <+> blue (pretty "~") <+> pretty t) (prettyCtx ctx)
    where prettyCtx ctx
            =  if (Context.null ctx) then [] else [nest 2 (vsep [pretty "Local bindings:", pretty ctx])]

instance PrettyPrec ElabError
