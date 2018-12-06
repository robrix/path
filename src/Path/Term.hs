{-# LANGUAGE DeriveFunctor, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Data.Text.Prettyprint.Doc
import Path.FreeVariables
import Path.Pretty
import Path.Recursive

newtype Term f = Term { out :: f (Term f) }

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)
deriving instance Show (f (Term f)) => Show (Term f)
deriving instance PrettyPrec (f (Term f)) => PrettyPrec (Term f)

instance PrettyPrec (f (Term f)) => Pretty (Term f) where
  pretty = prettyPrec 0

instance FreeVariables1 f => FreeVariables (Term f) where
  fvs = liftFvs fvs . out

instance Functor f => Recursive f (Term f) where project = out


data Ann f a = Ann { syn :: f (Ann f a), ann :: a }
  deriving (Functor)

deriving instance (Eq a, Eq (f (Ann f a))) => Eq (Ann f a)
deriving instance (Ord a, Ord (f (Ann f a))) => Ord (Ann f a)
deriving instance (Show a, Show (f (Ann f a))) => Show (Ann f a)

instance (PrettyPrec a, PrettyPrec (f (Ann f a))) => PrettyPrec (Ann f a) where
  prettyPrec d (Ann core ty) = prettyParens (d > 0) $ prettyPrec 1 core <> pretty " : " <> prettyPrec 1 ty

instance FreeVariables1 f => FreeVariables1 (Ann f) where
  liftFvs fvs (Ann tm ty) = liftFvs (liftFvs fvs) tm <> fvs ty

instance (FreeVariables a, FreeVariables1 f) => FreeVariables (Ann f a) where
  fvs = fvs1

erase :: Functor f => Ann f a -> Term f
erase = Term . fmap erase . syn
