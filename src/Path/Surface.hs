{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Path.Surface where

import Data.Text.Prettyprint.Doc
import Path.Core
import Path.FreeVariables
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Term

data Surface a
  = Core (Core a)
  | Ann a a
  deriving (Eq, Functor, Ord, Show)

instance (FreeVariables a, PrettyPrec a) => PrettyPrec (Surface a) where
  prettyPrec d (Core core) = prettyPrec d core
  prettyPrec d (Ann tm ty) = prettyParens (d > 0) $ prettyPrec 1 tm <> pretty " : " <> prettyPrec 0 ty

instance FreeVariables1 Surface where
  liftFvs fvs (Core core) = liftFvs fvs core
  liftFvs fvs (Ann tm ty) = fvs tm <> fvs ty

instance FreeVariables a => FreeVariables (Surface a) where
  fvs = fvs1

(-->) :: (String, Plicity, Term Surface a) -> Term Surface a -> Term Surface a
(n, e, a) --> b = Term (Core (Pi n e a b))

infixr 0 -->

typeT :: Term Surface a
typeT = Term (Core Type)

global :: String -> Term Surface a
global = Term . Core . Free . Global

var :: String -> Term Surface a
var = Term . Core . Bound

lam :: String -> Term Surface a -> Term Surface a
lam n = Term . Core . Lam n

(.:)  :: Term Surface a -> Term Surface a -> Term Surface a
a .: t = Term (Ann a t)

(#) :: Term Surface a -> Term Surface a -> Term Surface a
f # a = Term (Core (f :@ a))


subst :: String -> Term Surface a -> Term Surface a -> Term Surface a
subst i r (Term (Ann e t)) = Term (Ann (subst i r e) (subst i r t))
subst i r (Term (Core (Bound j)))
  | i == j    = r
  | otherwise = Term (Core (Bound j))
subst _ _ (Term (Core (Free n))) = Term (Core (Free n))
subst i r (Term (Core (Lam n b)))
  | i == n    = Term (Core (Lam n b))
  | otherwise = Term (Core (Lam n (subst i r b)))
subst i r (Term (Core (f :@ a))) = Term (Core (subst i r f :@ subst i r a))
subst _ _ (Term (Core Type)) = Term (Core Type)
subst i r (Term (Core (Pi n e t t')))
  | i == n    = Term (Core (Pi n e (subst i r t) t'))
  | otherwise = Term (Core (Pi n e (subst i r t) (subst i r t')))


identity :: Term Surface a
identity = lam "0" (var "0")

constant :: Term Surface a
constant = lam "1" (lam "0" (var "1"))
