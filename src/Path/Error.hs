{-# LANGUAGE LambdaCase #-}
module Path.Error where

import Data.Foldable (fold)
import Path.Context
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


data ElabError
  = FreeVariable QName Span
  | TypeMismatch Equation [Step] Context Span
  | NoRuleToInfer Context Span
  | IllegalApplication Type Span
  | ResourceMismatch Name Usage Usage Span [Span]
  | TypedHole QName Type Context Span
  | InfiniteType QName Type Span
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty = \case
    FreeVariable name span -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) []
    TypeMismatch (expected :===: actual) steps ctx span -> prettyErr span (fold (punctuate hardline
      [ pretty "type mismatch"
      , pretty "expected:" <+> pretty expected
      , pretty "  actual:" <+> pretty actual
      ])) (prettyCtx ctx : map prettyStep steps)
    NoRuleToInfer ctx span -> prettyErr span (pretty "no rule to infer type of term") [prettyCtx ctx]
    IllegalApplication ty span -> prettyErr span (pretty "illegal application of term of type" <+> pretty ty) []
    ResourceMismatch n pi used span spans -> prettyErr span msg (map prettys spans)
      where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length spans)) <+> pretty "than required" <+> parens (pretty pi)
    TypedHole n ty ctx span -> prettyErr span msg [prettyCtx ctx]
      where msg = pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
    InfiniteType n t span -> prettyErr span (pretty "Cannot construct infinite type" <+> pretty n <+> blue (pretty "~") <+> pretty t) []
    where prettyCtx ctx = nest 2 $ vsep
            [ pretty "Local bindings:"
            , pretty ctx
            ]
          prettyStep step = magenta (bold (pretty "via")) <+> align (pretty step)

instance PrettyPrec ElabError
