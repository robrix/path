{-# LANGUAGE FlexibleContexts #-}
module Path.Error where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader
import Data.Foldable (fold, toList)
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Core
import Path.Constraint
import Path.Name
import Path.Pretty
import Path.Span (Span, Spanned(..))

freeVariables :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Pretty name) => NonEmpty name -> m a
freeVariables names = do
  span <- ask
  throwError (prettyErr span (pretty "free variable" <> (if length names == 1 then mempty else pretty "s") <+> fillSep (punctuate comma (map pretty (toList names)))) [])

ambiguousName :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => User -> NonEmpty Qualified -> m a
ambiguousName name sources = do
  span <- ask
  throwError (prettyErr span (pretty "ambiguous name" <+> squotes (pretty name)) [nest 2 (vsep
    ( pretty "it could refer to"
    : map pretty (toList sources)))])


unsimplifiableConstraints :: (Carrier sig m, Member (Error Doc) sig) => Signature -> [Spanned (Constraint Core (Name Meta))] -> m a
unsimplifiableConstraints sig constraints = throwError (fold (intersperse hardline (map unsimplifiable constraints)))
  where unsimplifiable (c :~ span) = prettyErr span (pretty "unsimplifiable constraint") [pretty (sigFor c) <> pretty c]
        sigFor c = let fvs' = metaNames (localNames (fvs c)) in Signature (Map.filterWithKey (\ k _ -> k `Set.member` fvs') (unSignature sig))


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


unsolvedMetavariables :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Pretty ty, Foldable t) => ty -> t Meta -> m a
unsolvedMetavariables ty metas = do
  span <- ask
  throwError (prettyErr span (pretty "unsolved metavariable" <> (if length metas == 1 then mempty else pretty "s") <+> fillSep (punctuate comma (map pretty (toList metas)))) [pretty ty])
