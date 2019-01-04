module Path.Error where

import Data.Foldable (fold, toList)
import Path.Back
import Path.Context as Context
import Path.Name
import Path.Pretty
import Path.Type
import Path.Usage
import Text.Trifecta.Rendering (Span)

data Step
  = U Equation
  | C (Typed Span)
  | I Span
  deriving (Eq, Ord, Show)

instance Pretty Step where
  pretty (U eqn)          = pretty eqn
  pretty (C (span ::: t)) = prettyInfo span (pretty "checking against" <+> pretty t) []
  pretty (I span)         = prettyInfo span (pretty "infering") []

instance PrettyPrec Step


data ElabError = ElabError
  { errorSpan         :: Span
  , errorContext      :: Context
  , errorExistentials :: [Typed Meta]
  , errorSolutions    :: Back Solution
  , errorReason       :: ErrorReason
  }
  deriving (Eq, Ord, Show)

data ErrorReason
  = FreeVariable QName
  | TypeMismatch Equation [Step]
  | NoRuleToInfer
  | IllegalApplication Type
  | ResourceMismatch Name Usage Usage [Span]
  | TypedHole QName Type
  | InfiniteType QName Type
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (ElabError span ctx existentials solutions reason) = case reason of
    FreeVariable name -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) (prettyCtx ctx)
    TypeMismatch (expected :===: actual) steps -> prettyErr span (fold (punctuate hardline
      [ pretty "type mismatch"
      , pretty "expected:" <+> pretty expected
      , pretty "  actual:" <+> pretty actual
      ])) (map prettyStep steps <> prettyCtx ctx)
    NoRuleToInfer -> prettyErr span (pretty "no rule to infer type of term") (prettyCtx ctx)
    IllegalApplication ty -> prettyErr span (pretty "illegal application of term of type" <+> pretty ty) (prettyCtx ctx)
    ResourceMismatch n pi used spans -> prettyErr span msg (map prettys spans)
      where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length spans)) <+> pretty "than required" <+> parens (pretty pi)
    TypedHole n ty -> prettyErr span msg (prettyCtx ctx)
      where msg = pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
    InfiniteType n t -> prettyErr span (pretty "Cannot construct infinite type" <+> pretty n <+> blue (pretty "~") <+> pretty t) (prettyCtx ctx)
    where prettyCtx ctx
            =  unless (Context.null ctx)          "Local bindings" [pretty ctx]
            <> unless (Prelude.null existentials) "Existentials"   (map prettyExistential existentials)
            <> unless (Prelude.null solutions)    "Solutions"      (map pretty (toList solutions))
          unless c t d = if c then [] else [nest 2 (vsep (pretty t <> colon : d))]
          prettyStep step = magenta (bold (pretty "via")) <+> align (pretty step)
          prettyExistential (m ::: t) = pretty "∃" <+> green (pretty m) <+> colon <+> pretty t

instance PrettyPrec ElabError
