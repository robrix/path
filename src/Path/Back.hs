{-# LANGUAGE DeriveTraversable, LambdaCase #-}
module Path.Back where

import Prelude hiding (lookup)

data Back a = Nil | Back a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Semigroup (Back a) where
  as  <> Nil     = as
  Nil <> bs      = bs
  as  <> bs :> b = (as <> bs) :> b

instance Monoid (Back a) where
  mempty = Nil
  mappend = (<>)


lookup :: Eq a => a -> Back (a, b) -> Maybe b
lookup k = \case
  b :> (k', v)
    | k == k'   -> Just v
    | otherwise -> lookup k b
  Nil           -> Nothing
