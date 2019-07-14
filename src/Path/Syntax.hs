{-# LANGUAGE DeriveTraversable, TypeOperators #-}
module Path.Syntax where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Path.Pretty

data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable (:::) where
  bifoldMap f g (a ::: b) = f a <> g b

instance Bifunctor (:::) where
  bimap f g (a ::: b) = f a ::: g b

instance Bitraversable (:::) where
  bitraverse f g (a ::: b) = (:::) <$> f a <*> g b

typedTerm :: a ::: b -> a
typedTerm (a ::: _) = a

typedType :: a ::: b -> b
typedType (_ ::: t) = t

infix 7 :::

instance (Pretty a, Pretty b) => Pretty (a ::: b) where
  pretty (a ::: t) = pretty a <+> cyan colon <+> pretty t


data a := b = a := b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 1 :=

instance Bifoldable (:=) where
  bifoldMap f g (a := b) = f a <> g b

instance Bifunctor (:=) where
  bimap f g (a := b) = f a := g b

instance Bitraversable (:=) where
  bitraverse f g (a := b) = (:=) <$> f a <*> g b

instance (Pretty a, Pretty b) => Pretty (a := b) where
  pretty (a := b) = pretty a <+> magenta (pretty "=") <+> pretty b


-- | A functor composing two functors on the inside of a bifunctor. Can be used with @-XDerivingVia@ to derive 'Foldable', 'Functor', and 'Traversable' instances given 'Bifoldable', 'Bifunctor', and 'Bitraversable' instances for @p@ respectively.
newtype Comp2 p f g a = Comp2 { unComp2 :: p (f a) (g a) }

instance (Bifoldable p, Foldable f, Foldable g) => Foldable (Comp2 p f g) where
  foldMap f = bifoldMap (foldMap f) (foldMap f) . unComp2

instance (Bifunctor p, Functor f, Functor g) => Functor (Comp2 p f g) where
  fmap f = Comp2 . bimap (fmap f) (fmap f) . unComp2
