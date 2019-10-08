{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, QuantifiedConstraints, StandaloneDeriving, TypeOperators #-}
module Path.Surface where

import Control.Monad (ap)
import Control.Monad.Trans
import GHC.Generics (Generic1)
import Path.Name
import Path.Plicity
import Path.Span
import Path.Syntax
import Syntax.Module
import Syntax.Scope

data Surface a
  = Var a
  | Lam (Plicit (Ignored (Maybe User))) (Spanned (Scope () Surface a))
  | Spanned (Surface a) :$ Plicit (Spanned (Surface a))
  | Type
  | Pi (Plicit (Ignored (Maybe User) ::: Spanned (Surface a))) (Spanned (Scope () Surface a))
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

instance Applicative Surface where
  pure = Var
  (<*>) = ap

instance Monad Surface where
  Var a   >>= f = f a
  Lam p b >>= f = Lam p (fmap (>>=* f) b)
  g :$ a  >>= f = (fmap (>>= f) g) :$ (fmap (fmap (>>= f)) a)
  Type    >>= _ = Type
  Pi t b  >>= f = Pi (fmap (fmap (fmap (>>= f))) t) (fmap (>>=* f) b)


lam :: Eq a => Plicit (Named (Maybe User) a) -> Spanned (Surface a) -> Surface a
lam (p :< Named u n) b = Lam (p :< u) (abstract1 n <$> b)

lam' :: Plicit (Maybe User) -> Spanned (Surface User) -> Surface User
lam' (p :< Nothing) b = Lam (p :< Ignored Nothing) (lift <$> b)
lam' (p :< Just n)  b = lam (p :< named (Just n) n) b


pi :: Eq a => Plicit (Named (Maybe User) a ::: Spanned (Surface a)) -> Spanned (Surface a) -> Surface a
pi (p :< Named u n ::: t) b = Pi (p :< u ::: t) (abstract1 n <$> b)

(-->) :: Spanned (Surface a) -> Spanned (Surface a) -> Surface a
t --> b = Pi (Ex :< Ignored Nothing ::: t) (lift <$> b)

infixr 0 -->
