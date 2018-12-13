module Path.AlphaEquivalent where

class AlphaEquivalent a where
  aeq :: a -> a -> Bool
