{-# LANGUAGE FlexibleContexts #-}
module Path.Error where

import Control.Effect.Error
import Control.Effect.Reader
import Data.Foldable (fold, toList)
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Set as Set
import Path.Name
import Path.Pretty
import Path.Span (Span, Spanned(..))

freeVariables :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Ord name, Pretty name) => NonEmpty name -> m a
freeVariables names = do
  span <- ask
  throwError (prettyErr span (pretty "free variable" <> (if length names == 1 then mempty else pretty "s") <+> fillSep (punctuate comma (map pretty (toList (foldMap Set.singleton names))))) [])

ambiguousName :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => User -> NonEmpty Qualified -> m a
ambiguousName name sources = do
  span <- ask
  throwError (prettyErr span (pretty "ambiguous name" <+> squotes (pretty name)) [nest 2 (vsep
    ( pretty "it could refer to"
    : map pretty (toList sources)))])


unknownModule :: (Carrier sig m, Member (Error Doc) sig) => Spanned ModuleName -> m a
unknownModule (name :~ span) = throwError (prettyErr span (pretty "Could not find module" <+> squotes (pretty name)) [])

cyclicImport :: (Carrier sig m, Member (Error Doc) sig) => NonEmpty (Spanned ModuleName) -> m a
cyclicImport (name :~ span :| [])    = throwError (prettyErr span (pretty "Cyclic import of" <+> squotes (pretty name)) [])
cyclicImport (name :~ span :| names) = throwError (vsep
  ( prettyErr span (pretty "Cyclic import of" <+> squotes (pretty name) <> colon) []
  : foldr ((:) . whichImports) [ whichImports (name :~ span) ] names))
  where whichImports (name :~ span) = prettyInfo span (pretty "which imports" <+> squotes (pretty name) <> colon) []


unsimplifiable :: (Carrier sig m, Member (Error Doc) sig, Pretty a) => [Spanned a] -> m a
unsimplifiable constraints = throwError (fold (intersperse hardline (map format constraints)))
  where format (c :~ span) = prettyErr span (pretty "unsimplifiable constraint") [pretty c]


unsolvedMetavariables :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Pretty ty, Pretty v, Foldable t) => ty -> t v -> m a
unsolvedMetavariables ty metas = do
  span <- ask
  throwError (prettyErr span (pretty "unsolved metavariable" <> (if length metas == 1 then mempty else pretty "s") <+> fillSep (punctuate comma (map pretty (toList metas)))) [pretty ty])
