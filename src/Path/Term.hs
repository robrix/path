{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

data Term f a
  = Var a
  | Term (f (Term f) a)

deriving instance (Eq   a, Eq   (f (Term f) a)) => Eq   (Term f a)
deriving instance (Ord  a, Ord  (f (Term f) a)) => Ord  (Term f a)
deriving instance (Show a, Show (f (Term f) a)) => Show (Term f a)
