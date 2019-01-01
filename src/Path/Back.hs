{-# LANGUAGE DeriveTraversable, LambdaCase #-}
module Path.Back where

import Prelude hiding (filter, lookup)

data Back a = Nil | Back a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :>

instance Semigroup (Back a) where
  as  <> Nil       = as
  Nil <> bs        = bs
  as  <> (bs :> b) = (as <> bs) :> b

instance Monoid (Back a) where
  mempty = Nil
  mappend = (<>)


find :: (a -> Bool) -> Back a -> Maybe a
find p = \case
  b :> a
    | p a       -> Just a
    | otherwise -> find p b
  Nil           -> Nothing


filter :: (a -> Bool) -> Back a -> Back a
filter keep = \case
  as :> a
    | keep a    -> filter keep as :> a
    | otherwise -> filter keep as
  Nil           -> Nil


zipWith :: (a -> b -> c) -> Back a -> Back b -> Back c
zipWith f = curry go
  where go = \case
          (Nil,     _)       -> Nil
          (_,       Nil)     -> Nil
          (as :> a, bs :> b) -> go (as, bs) :> f a b
