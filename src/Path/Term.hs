{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Path.FreeVariables
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen

newtype Term f = In { out :: f (Term f) }

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)
deriving instance Show (f (Term f)) => Show (Term f)
deriving instance PrettyPrec (f (Term f)) => PrettyPrec (Term f)

instance PrettyPrec (f (Term f)) => Pretty (Term f) where
  pretty = prettyPrec 0

instance FreeVariables1 f => FreeVariables (Term f) where
  fvs = liftFvs fvs . out


data Ann f a b = Ann { syn :: f b, ann :: a }
  deriving (Eq, Functor, Ord, Show)

instance (PrettyPrec a, PrettyPrec (f b)) => PrettyPrec (Ann f a b) where
  prettyPrec d (Ann core ty) = prettyParens (d > 0) $ prettyPrec 1 core <> pretty " : " <> prettyPrec 1 ty

instance (FreeVariables a, FreeVariables1 f) => FreeVariables1 (Ann f a) where
  liftFvs fvs' (Ann tm ty) = liftFvs fvs' tm <> fvs ty

instance (FreeVariables a, FreeVariables b, FreeVariables1 f) => FreeVariables (Ann f a b) where
  fvs = fvs1

erase :: Functor f => Term (Ann f a) -> Term f
erase = In . fmap erase . syn . out
