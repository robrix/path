{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Path.Name
import Path.Pretty
import Text.Trifecta.Rendering (Span)

data Term f = In { out :: f (Term f), ann :: Span }

deriving instance (Eq   (f (Term f))) => Eq   (Term f)
deriving instance (Ord  (f (Term f))) => Ord  (Term f)
deriving instance (Show (f (Term f))) => Show (Term f)

instance PrettyPrec (f (Term f)) => PrettyPrec (Term f) where
  prettyPrec d (In tm ty)
    | show ty' == "" = prettyPrec d tm
    | otherwise      = prettyParens (d > 0) $ prettyPrec 1 tm <> pretty " : " <> ty'
    where ty' = prettyPrec 1 ty

instance PrettyPrec (f (Term f)) => Pretty (Term f) where
  pretty = prettyPrec 0

cata :: Functor f => (f b -> Span -> b) -> Term f -> b
cata alg = go where go = alg . fmap go . out <*> ann

hoist :: Functor f => (forall x . f x -> g x) -> Term f -> Term g
hoist f = cata (In . f)

instance FreeVariables1 v f => FreeVariables v (Term f) where
  fvs (In out _) = liftFvs fvs out
