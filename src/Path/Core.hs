{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving #-}
module Path.Core where

import Control.Monad (ap)
import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

newtype Core a = Core { unCore :: CoreF Core a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data CoreF f a
  = Var (Name a)
  | Lam (Plicit (Maybe User)) (f (Incr (f a)))
  | f a :$ Plicit (f a)
  | Type
  | Pi Usage (f a) (f a)
  | Hole Gensym
  | Ann Span (f a)
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (CoreF f a)
deriving instance (Ord  a, forall x . Eq   x => Eq   (f x)
                         , forall x . Ord  x => Ord  (f x)) => Ord  (CoreF f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (CoreF f a)

instance Applicative Core where
  pure = Core . Var . Local
  (<*>) = ap

instance Monad Core where
  a >>= f = gfold (name id (Core . Var . Global)) (fmap Core . Lam) (fmap Core . (:$)) (Core Type) (fmap (fmap Core) . Pi) (Core . Hole) (fmap Core . Ann) pure (fmap f a)

lam :: Eq a => Plicit a -> Core a -> Core a
lam (p :< n) b = Core (Lam (p :< Nothing) (bind n b))

lams :: (Eq a, Foldable t) => t (Plicit a) -> Core a -> Core a
lams names body = foldr lam body names


gfold :: forall m n b
      .  (forall a . Name (m a) -> n a)
      -> (forall a . Plicit (Maybe User) -> n (Incr (n a)) -> n a)
      -> (forall a . n a -> Plicit (n a) -> n a)
      -> (forall a . n a)
      -> (forall a . Usage -> n a -> n a -> n a)
      -> (forall a . Gensym -> n a)
      -> (forall a . Span -> n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> Core (m b)
      -> n b
gfold var lam app ty pi hole ann k = go
  where go :: Core (m x) -> n x
        go = \case
          Core (Var a) -> var a
          Core (Lam n b) -> lam n (go (k . fmap go <$> b))
          Core (f :$ a) -> app (go f) (go <$> a)
          Core Type -> ty
          Core (Pi m t b) -> pi m (go t) (go b)
          Core (Hole a) -> hole a
          Core (Ann span a) -> ann span (go a)


-- | Substitute occurrences of a variable with a 'Core' within another 'Core'.
--
--   prop> substitute a (pure b) (Lam (pure (S a))) === Lam (pure (S b))
substitute :: Eq a => a -> Core a -> Core a -> Core a
substitute name image = instantiate image . bind name


-- | Bind occurrences of an 'Meta' in a 'Core' term, producing a 'Core' term in which the 'Meta' is bound.
bind :: Eq a => a -> Core a -> Core (Incr (Core a))
bind name = fmap (fmap pure . match name)

-- | Substitute a 'Core' term for the free variable in a given 'Core' term, producing a closed 'Core' term.
instantiate :: Core a -> Core (Incr (Core a)) -> Core a
instantiate t b = b >>= subst t
