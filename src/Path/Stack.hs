{-# LANGUAGE DeriveTraversable, LambdaCase #-}
module Path.Stack where

import Data.Foldable (foldl', toList)
import Path.Pretty
import Prelude hiding (filter, lookup)

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

instance Pretty a => PrettyPrec (Stack a)


fromList :: [a] -> Stack a
fromList = foldl' (:>) Nil

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

alignWith :: (a -> b -> c) -> Stack a -> Stack b -> (Maybe (Either (Stack a) (Stack b)), Stack c)
alignWith f = go
  where go Nil       Nil       = (Nothing, Nil)
        go (as :> a) Nil       = (Just (Left  (as :> a)), Nil)
        go Nil       (bs :> b) = (Just (Right (bs :> b)), Nil)
        go (as :> a) (bs :> b) = (:> f a b) <$> go as bs
