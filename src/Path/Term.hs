{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Data.Text.Prettyprint.Doc
import Path.FreeVariables
import Path.Pretty
import Path.Recursive

newtype Term f a = Term (f (Term f a))

deriving instance Eq (f (Term f a)) => Eq (Term f a)
deriving instance Ord (f (Term f a)) => Ord (Term f a)
deriving instance Show (f (Term f a)) => Show (Term f a)
deriving instance PrettyPrec (f (Term f a)) => PrettyPrec (Term f a)

instance PrettyPrec (f (Term f a)) => Pretty (Term f a) where
  pretty = prettyPrec 0

instance (FreeVariables1 f, Functor f) => FreeVariables (Term f a) where
  fvs = cata (liftFvs id)

instance Functor f => Recursive f (Term f a) where project (Term f) = f
