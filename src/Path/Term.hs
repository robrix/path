{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Path.FreeVariables
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen

data Term f a = In { out :: f (Term f a), ann :: a }

deriving instance (Eq   (f (Term f a)), Eq   a) => Eq   (Term f a)
deriving instance (Ord  (f (Term f a)), Ord  a) => Ord  (Term f a)
deriving instance (Show (f (Term f a)), Show a) => Show (Term f a)

instance (PrettyPrec (f (Term f a)), PrettyPrec a) => PrettyPrec (Term f a) where
  prettyPrec d (In tm ty) = prettyParens (d > 0) $ prettyPrec 1 tm <> pretty " : " <> prettyPrec 1 ty

instance (PrettyPrec (f (Term f a)), PrettyPrec a) => Pretty (Term f a) where
  pretty = prettyPrec 0

instance (FreeVariables1 f, FreeVariables a) => FreeVariables (Term f a) where
  fvs (In tm ty) = liftFvs fvs tm <> fvs ty

instance Functor f => Functor (Term f) where
  fmap f (In tm a) = In (fmap (fmap f) tm) (f a)
