{-# LANGUAGE MultiParamTypeClasses #-}
module Path.Semiring where

class Semigroup r => Semiring r where
  (><) :: r -> r -> r
  infixr 7 ><

zero :: Monoid r => r
zero = mempty

class (Monoid r, Semiring r) => Unital r where
  one :: r

class Semiring r => LeftModule r m where
  (><<) :: r -> m -> m
  infixr 7 ><<
