{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Error where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader
import Data.Foldable (fold, toList)
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty(..))
import Path.Constraint
import Path.Name
import Path.Pretty
import Text.Trifecta.Rendering (Span, Spanned(..))

freeVariable :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Pretty name) => name -> m a
freeVariable name = do
  span <- ask
  throwError (prettyErr span (pretty "free variable" <+> squotes (pretty name)) [])

ambiguousName :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => User -> NonEmpty Name -> m a
ambiguousName name sources = do
  span <- ask
  throwError (prettyErr span (pretty "ambiguous name" <+> squotes (pretty name)) [nest 2 (vsep
    ( pretty "it could refer to"
    : map prettyQName (toList sources)))])


unsimplifiableConstraint :: (Carrier sig m, Member (Error Doc) sig) => Spanned (Constraint Meta) -> m a
unsimplifiableConstraint (c :~ span) = throwError (prettyErr span (pretty "unsimplifiable constraint") [pretty c])

blockedConstraints :: (Carrier sig m, Member (Error Doc) sig, Member Naming sig) => [Spanned (Constraint Meta)] -> m a
blockedConstraints constraints = do
  cs <- traverse (blocked <*> toList . metaNames . fvs) constraints
  throwError (fold (intersperse hardline cs))
  where blocked (c :~ span) m = do
          (ctx, eqn) <- unbinds c
          pure (prettyErr span (pretty "constraint" </> pretty eqn </> pretty "blocked on metavars" <+> encloseSep mempty mempty (comma <> space) (map (green . pretty . Meta) m)) (prettyCtx ctx))

stalledConstraints :: (Carrier sig m, Member (Error Doc) sig, Member Naming sig) => [Spanned (Constraint Meta)] -> m a
stalledConstraints constraints = do
  cs <- traverse stalled constraints
  throwError (fold (intersperse hardline cs))
  where stalled (c :~ span) = do
          (ctx, eqn) <- unbinds c
          pure (prettyErr span (pretty "stalled constraint" </> pretty eqn) (prettyCtx ctx))


prettyCtx :: (Foldable t, Pretty (t a)) => t a -> [Doc]
prettyCtx ctx = if null ctx then [] else [nest 2 (vsep [pretty "Local bindings:", pretty ctx])]

prettyEqn :: (Pretty a, Pretty b) => Equation a ::: b -> Doc
prettyEqn ((expected :===: actual) ::: ty) = fold (punctuate hardline
  [ pretty "expected:" <+> pretty (expected ::: ty)
  , pretty "  actual:" <+> pretty (actual ::: ty)
  ])
