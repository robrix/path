module Path.Error where

import           Data.Foldable (fold, toList)
import qualified Data.Set as Set
import           Path.Constraint
import           Path.Context as Context
import           Path.Name
import           Path.Pretty
import           Path.Usage
import           Path.Value
import           Text.Trifecta.Rendering (Span)

data ElabError = ElabError
  { errorSpan    :: Span
  , errorContext :: Context
  , errorReason  :: ErrorReason
  }
  deriving (Eq, Ord, Show)

data ErrorReason
  = FreeVariable QName
  | TypeMismatch (Set.Set (Caused (Equation (Value MName))))
  | NoRuleToInfer
  | IllegalApplication (Type MName)
  | ResourceMismatch Gensym Usage Usage [Span]
  | TypedHole QName (Type MName)
  | InfiniteType QName (Type MName)
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (ElabError span ctx reason) = case reason of
    FreeVariable name -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) (prettyCtx ctx)
    TypeMismatch eqns -> prettyErr span (fold (punctuate hardline
      (pretty "type mismatch" : map prettyEqn (toList eqns)))) (prettyCtx ctx)
    NoRuleToInfer -> prettyErr span (pretty "no rule to infer type of term") (prettyCtx ctx)
    IllegalApplication ty -> prettyErr span (pretty "illegal application of term of type" <+> pretty ty) (prettyCtx ctx)
    ResourceMismatch n pi used uses -> prettyErr span msg (prettyCtx ctx <> map prettys uses)
      where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length uses)) <+> pretty "than required" <+> parens (pretty pi)
    TypedHole n ty -> prettyErr span msg (prettyCtx ctx)
      where msg = pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
    InfiniteType n t -> prettyErr span (pretty "Cannot construct infinite type" <+> pretty n <+> blue (pretty "~") <+> pretty t) (prettyCtx ctx)
    where prettyCtx ctx = if Context.null ctx then [] else [nest 2 (vsep [pretty "Local bindings:", pretty ctx])]
          prettyEqn (expected :===: actual :@ cause) = fold (punctuate hardline
            ( pretty "expected:" <+> pretty expected
            : pretty "  actual:" <+> pretty actual
            : prettyCause cause))
          prettyCause (Assert span) = [magenta (pretty "via source"), prettys span]
          prettyCause (Via eqn cause) = magenta (pretty "via") <+> pretty eqn : prettyCause cause
          prettyCause (l :<>: r) = prettyCause l <> prettyCause r

instance PrettyPrec ElabError
