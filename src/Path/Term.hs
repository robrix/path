{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Path.Name
import Path.Pretty

data Term f a = In { out :: f (Term f a), ann :: a }

deriving instance (Eq   (f (Term f a)), Eq   a) => Eq   (Term f a)
deriving instance (Ord  (f (Term f a)), Ord  a) => Ord  (Term f a)
deriving instance (Show (f (Term f a)), Show a) => Show (Term f a)

instance (PrettyPrec (f (Term f a)), PrettyPrec a) => PrettyPrec (Term f a) where
  prettyPrec d (In tm ty)
    | show ty' == "" = prettyPrec d tm
    | otherwise      = prettyParens (d > 0) $ prettyPrec 1 tm <> pretty " : " <> ty'
    where ty' = prettyPrec 1 ty

instance (PrettyPrec (f (Term f a)), PrettyPrec a) => Pretty (Term f a) where
  pretty = prettyPrec 0

instance Functor f => Functor (Term f) where
  fmap f (In tm a) = In (fmap (fmap f) tm) (f a)

cata :: Functor f => (f b -> a -> b) -> Term f a -> b
cata alg = go where go = alg . fmap go . out <*> ann

hoist :: Functor f => (forall x . f x -> g x) -> Term f a -> Term g a
hoist f = cata (In . f)

instance FreeVariables1 v f => FreeVariables v (Term f a) where
  fvs (In out _) = liftFvs fvs out
