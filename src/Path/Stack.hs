{-# LANGUAGE DeriveTraversable, LambdaCase #-}
module Path.Stack where

import Data.Foldable (toList)
import Path.Pretty
import Prelude hiding (drop, filter, lookup)

data Stack a = Nil | Stack a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :>

instance Semigroup (Stack a) where
  as  <> Nil       = as
  Nil <> bs        = bs
  as  <> (bs :> b) = (as <> bs) :> b

instance Monoid (Stack a) where
  mempty = Nil
  mappend = (<>)

instance Pretty a => Pretty (Stack a) where
  pretty = list . toList . fmap pretty


find :: (a -> Bool) -> Stack a -> Maybe a
find p = \case
  b :> a
    | p a       -> Just a
    | otherwise -> find p b
  Nil           -> Nothing


filter :: (a -> Bool) -> Stack a -> Stack a
filter keep = \case
  as :> a
    | keep a    -> filter keep as :> a
    | otherwise -> filter keep as
  Nil           -> Nil

drop :: Int -> Stack a -> Stack a
drop n (xs :> _) | n > 0 = drop (pred n) xs
drop _ xs                = xs

head :: Stack a -> a
head (_ :> a) = a
head _        = error "Path.Stack.head: empty stack"

tail :: Stack a -> Stack a
tail (as :> _) = as
tail _         = error "Path.Stack.tail: empty stack"
