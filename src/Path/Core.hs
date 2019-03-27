{-# LANGUAGE DeriveTraversable, LambdaCase, RankNTypes, ScopedTypeVariables #-}
module Path.Core where

import Control.Monad (ap)
import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

data Core a
  = Var a
  | Lam (Maybe User) (Scope a)
  | Core a :$ Core a
  | Type
  | Pi (Maybe User) Plicity Usage (Core a) (Scope a)
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
lam n b = Lam Nothing (bind n b)

lams :: (Eq a, Foldable t) => t a -> Core a -> Core a
lams names body = foldr lam body names


gfoldT :: forall m n b
       .  (forall a . m a -> n a)
       -> (forall a . Maybe User -> n (Incr a) -> n a)
       -> (forall a . n a -> n a -> n a)
       -> (forall a . n a)
       -> (forall a . Maybe User -> Plicity -> Usage -> n a -> n (Incr a) -> n a)
       -> (forall a . m a -> n a)
       -> (forall a . Span -> n a -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Core (m b)
       -> n b
gfoldT var lam app ty pi hole ann dist = go
  where go :: Core (m x) -> n x
        go = \case
          Var a -> var a
          Lam n (Scope b) -> lam n (go (dist <$> b))
          f :$ a -> app (go f) (go a)
          Type -> ty
          Pi n p m t (Scope b) -> pi n p m (go t) (go (dist <$> b))
          Hole a -> hole a
          Ann span a -> ann span (go a)

joinT :: Core (Core a) -> Core a
joinT = gfoldT id (\ n -> Lam n . Scope) (:$) Type (\ n p m t -> Pi n p m t . Scope) id Ann (incr (pure Z) (fmap S))


-- | Substitute occurrences of a variable with a 'Core' within another 'Core'.
--
--   prop> substitute a (pure b) (Lam (Scope (pure (S a)))) === Lam (Scope (pure (S b)))
substitute :: Eq a => a -> Core a -> Core a -> Core a
substitute name image = instantiate image . bind name


-- | Bind occurrences of an 'Meta' in a 'Core' term, producing a 'Scope' in which the 'Meta' is bound.
bind :: Eq a => a -> Core a -> Scope a
bind name = Scope . fmap (match name)

-- | Substitute a 'Core' term for the free variable in a given 'Scope', producing a closed 'Core' term.
instantiate :: Core a -> Scope a -> Core a
instantiate t (Scope b) = b >>= subst t . fmap pure
