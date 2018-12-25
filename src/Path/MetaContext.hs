{-# LANGUAGE DeriveTraversable #-}
module Path.MetaContext where

data Back a = Nil | Back a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Semigroup (Back a) where
  as  <> Nil     = as
  Nil <> bs      = bs
  as  <> bs :> b = (as <> bs) :> b

instance Monoid (Back a) where
  mempty = Nil
  mappend = (<>)
