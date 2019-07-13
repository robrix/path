{-# LANGUAGE FlexibleInstances, RankNTypes, TypeOperators #-}
module Path.Term where

import Control.Effect.Carrier
import Control.Effect.Sum
import Path.Scope

data Term sig a
  = Var a
  | Term (sig (Term sig) a)


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
