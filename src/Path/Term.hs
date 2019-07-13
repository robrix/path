{-# LANGUAGE FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Term where

import Control.Effect.Carrier
import Control.Effect.Sum
import Path.Scope

data Term sig a
  = Var a
  | Term (sig (Term sig) a)


iter :: forall m n sig a b
     .  Syntax sig
     => (forall a . m a -> n a)
     -> (forall a . sig n a -> n a)
     -> (forall a . Incr () (n a) -> m (Incr () (n a)))
     -> (a -> m b)
     -> Term sig a
     -> n b
iter var alg bound = go
  where go :: forall x y . (x -> m y) -> Term sig x -> n y
        go free = \case
          Var a -> var (free a)
          Term t -> alg (foldSyntax go bound free t)


class HFunctor sig => Syntax sig where
  foldSyntax :: (forall x y . (x -> m y) -> f x -> n y)
             -> (forall a . Incr () (n a) -> m (Incr () (n a)))
             -> (a -> m b)
             -> sig f a
             -> sig n b

instance Syntax (Scope ()) where
  foldSyntax go bound free = Scope . go (bound . fmap (go free)) . unScope

instance (Syntax l, Syntax r) => Syntax (l :+: r) where
  foldSyntax go bound free (L l) = L (foldSyntax go bound free l)
  foldSyntax go bound free (R r) = R (foldSyntax go bound free r)
