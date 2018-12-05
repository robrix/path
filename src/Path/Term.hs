{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Path.FreeVariables
import Path.Recursive

newtype Term f = Term (f (Term f))

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)

instance (FreeVariables1 f, Functor f) => FreeVariables (Term f) where
  fvs = cata (liftFvs id)

instance Functor f => Recursive f (Term f) where project (Term f) = f