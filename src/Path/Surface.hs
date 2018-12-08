{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Path.Surface where

import Path.Core
import Path.FreeVariables
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Term
import Text.PrettyPrint.ANSI.Leijen

data Surface a
  = Core (Core a)
  | a ::: a
  deriving (Eq, Functor, Ord, Show)

instance (FreeVariables a, PrettyPrec a) => PrettyPrec (Surface a) where
  prettyPrec d (Core core) = prettyPrec d core
  prettyPrec d (tm ::: ty) = prettyParens (d > 0) $ prettyPrec 1 tm <> pretty " : " <> prettyPrec 0 ty

instance FreeVariables1 Surface where
  liftFvs fvs (Core core) = liftFvs fvs core
  liftFvs fvs (tm ::: ty) = fvs tm <> fvs ty

instance FreeVariables a => FreeVariables (Surface a) where
  fvs = fvs1

(-->) :: (String, Plicity, Term Surface) -> Term Surface -> Term Surface
(n, e, a) --> b = In (Core (Pi n e a b))

infixr 0 -->

typeT :: Term Surface
typeT = In (Core Type)

global :: String -> Term Surface
global = In . Core . Free . Global

var :: String -> Term Surface
var = In . Core . Bound

lam :: String -> Term Surface -> Term Surface
lam n = In . Core . Lam n

(.:)  :: Term Surface -> Term Surface -> Term Surface
a .: t = In (a ::: t)

(#) :: Term Surface -> Term Surface -> Term Surface
f # a = In (Core (f :@ a))


subst :: String -> Term Surface -> Term Surface -> Term Surface
subst i r (In (e ::: t)) = In (subst i r e ::: subst i r t)
subst i r (In (Core (Bound j)))
  | i == j    = r
  | otherwise = In (Core (Bound j))
subst _ _ (In (Core (Free n))) = In (Core (Free n))
subst i r (In (Core (Lam n b)))
  | i == n    = In (Core (Lam n b))
  | otherwise = In (Core (Lam n (subst i r b)))
subst i r (In (Core (f :@ a))) = In (Core (subst i r f :@ subst i r a))
subst _ _ (In (Core Type)) = In (Core Type)
subst i r (In (Core (Pi n e t t')))
  | i == n    = In (Core (Pi n e (subst i r t) t'))
  | otherwise = In (Core (Pi n e (subst i r t) (subst i r t')))
