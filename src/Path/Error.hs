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
import Path.Constraint
import Path.Name
import Path.Pretty
import Path.Scope
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


unsimplifiableConstraints :: (Carrier sig m, Member (Error Doc) sig) => Signature -> Substitution -> [Spanned (Constraint Meta)] -> m a
unsimplifiableConstraints sig subst constraints = throwError (metas <> fold (intersperse hardline (map unsimplifiable constraints)))
  where unsimplifiable (c :~ span) = prettyErr span (pretty "unsimplifiable constraint") [pretty (sigFor c) <> pretty c]
        metas = encloseSep (magenta (pretty "Θ") <> space) mempty (cyan comma <> space) (map (uncurry prettyBind) (Map.toList entries)) <> if Prelude.null entries then mempty else hardline
        entries = foldr (uncurry define) (Entry . (Nothing :::) <$> unSignature sig) (Map.toList (unSubstitution subst))
        prettyBind m t = pretty (Meta m) <+> pretty t
        define m v = Map.update (\ e -> Just (Entry (Just v ::: entryType e))) m
        sigFor c = let fvs' = metaNames (fvs c) in Signature (Map.filterWithKey (\ k _ -> k `Set.member` fvs') (unSignature sig))
