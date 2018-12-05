{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Path.Recursive

newtype Term f = Term (f (Term f))

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)

instance Functor f => Recursive f (Term f) where project (Term f) = f
