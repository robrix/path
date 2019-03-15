{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Core where

import Control.Effect
import Control.Monad (ap)
import Data.Foldable (toList)
import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

data Core a
  = Var a
  | Lam (Scope a)
  | Core a :$ Core a
  | Type
  | Pi Plicity Usage (Core a) (Scope a)
  | Hole a
  | Ann Span (Core a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Core (Incr a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Core where
  pure = Var
  (<*>) = ap

instance Monad Core where
  a >>= f = joinT (fmap f a)

lam :: Eq a => a -> Core a -> Core a
lam n b = Lam (bind n b)

lams :: (Eq a, Foldable t) => t a -> Core a -> Core a
lams names body = foldr lam body names

pi :: Eq a => (a, Plicity, Usage) ::: Core a -> Core a -> Core a
pi ((n, p, u) ::: t) b = Pi p u t (bind n b)

pis :: (Eq a, Foldable t) => t ((a, Plicity, Usage) ::: Core a) -> Core a -> Core a
pis names body = foldr pi body names


gfoldT :: forall m n b
       .  (forall a . m a -> n a)
       -> (forall a . n (Incr a) -> n a)
       -> (forall a . n a -> n a -> n a)
       -> (forall a . n a)
       -> (forall a . Plicity -> Usage -> n a -> n (Incr a) -> n a)
       -> (forall a . m a -> n a)
       -> (forall a . Span -> n a -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Core (m b)
       -> n b
gfoldT var lam app ty pi hole ann dist = go
  where go :: Core (m x) -> n x
        go = \case
          Var a -> var a
          Lam (Scope b) -> lam (go (dist <$> b))
          f :$ a -> app (go f) (go a)
          Type -> ty
          Pi p m t (Scope b) -> pi p m (go t) (go (dist <$> b))
          Hole a -> hole a
          Ann span a -> ann span (go a)


joinT :: Core (Core a) -> Core a
joinT = gfoldT id (Lam . Scope) (:$) Type (\ p m t -> Pi p m t . Scope) id Ann (incr (pure Z) (fmap S))


instance Ord a => FreeVariables a (Core a) where
  fvs = foldMap Set.singleton

uses :: Gensym -> Core Qual -> [Span]
uses n = run . runNaming (Root "pretty") . go Nothing
  where go span = \case
          Var n'
            | Local n == n' -> pure (toList span)
            | otherwise     -> pure []
          Lam b -> gensym "" >>= \ n -> go span (instantiate (pure (Local n)) b)
          f :$ a -> (<>) <$> go span f <*> go span a
          Type -> pure []
          Pi _ _ t b -> gensym "" >>= \ n -> (<>) <$> go span t <*> go span (instantiate (pure (Local n)) b)
          Hole n'
            | Local n == n' -> pure (toList span)
            | otherwise     -> pure []
          Ann span a -> go (Just span) a


-- | Bind occurrences of a 'Name' in a 'Core' term, producing a 'Scope' in which the 'Name' is bound.
bind :: Eq a => a -> Core a -> Scope a
bind name = Scope . fmap (match name)

-- | Substitute a 'Core' term for the free variable in a given 'Scope', producing a closed 'Core' term.
instantiate :: Core a -> Scope a -> Core a
instantiate t (Scope b) = b >>= subst t . fmap Var
