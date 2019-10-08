{-# LANGUAGE DeriveTraversable, LambdaCase #-}
module Path.Stack where

import Syntax.Stack

find :: (a -> Bool) -> Stack a -> Maybe a
find p = \case
  b :> a
    | p a       -> Just a
    | otherwise -> find p b
  Nil           -> Nothing
