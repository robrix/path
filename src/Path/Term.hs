{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Data.Text.Prettyprint.Doc
import Path.FreeVariables
import Path.Pretty
import Path.Recursive

newtype Term f = Term (f (Term f))

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)
deriving instance Show (f (Term f)) => Show (Term f)
deriving instance PrettyPrec (f (Term f)) => PrettyPrec (Term f)

instance PrettyPrec (f (Term f)) => Pretty (Term f) where
  pretty = prettyPrec 0

instance (FreeVariables1 f, Functor f) => FreeVariables (Term f) where
  fvs = cata (liftFvs id)

instance Functor f => Recursive f (Term f) where project (Term f) = f
