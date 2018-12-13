module Path.AlphaEquivalent where

class AlphaEquivalent a where
  aeq :: a -> a -> Bool

class AlphaEquivalent1 t where
  liftAeq :: (a -> b -> Bool) -> t a -> t b -> Bool
