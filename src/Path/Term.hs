{-# LANGUAGE DeriveFunctor, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import qualified Data.Set as Set
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen

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


class AlphaEquivalent a where
  aeq :: a -> a -> Bool

class AlphaEquivalent1 t where
  liftAeq :: (a -> b -> Bool) -> t a -> t b -> Bool

instance AlphaEquivalent1 f => AlphaEquivalent (Term f a) where
  aeq (In syn1 _) (In syn2 _) = liftAeq aeq syn1 syn2


class Ord v => FreeVariables v a where
  fvs :: a -> Set.Set v

class Ord v => FreeVariables1 v t where
  liftFvs :: (a -> Set.Set v) -> t a -> Set.Set v

instance (FreeVariables1 v f, FreeVariables v a) => FreeVariables v (Term f a) where
  fvs (In out ann) = liftFvs fvs out <> fvs ann

instance Ord v => FreeVariables v () where
  fvs _ = Set.empty

instance (FreeVariables v a, FreeVariables v b) => FreeVariables v (a, b) where
  fvs (a, b) = fvs a <> fvs b

instance FreeVariables v a => FreeVariables v [a] where
  fvs = foldMap fvs
