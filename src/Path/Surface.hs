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

(-->) :: Semigroup ann => (String, Plicity, Term (Ann Surface ann)) -> Term (Ann Surface ann) -> Term (Ann Surface ann)
(n, e, a) --> b = In (Ann (Core (Pi n e a b)) (ann (out a) <> ann (out b)))

infixr 0 -->

typeT :: Surface a
typeT = Core Type

global :: String -> Surface a
global = Core . Free . Global

var :: String -> Surface a
var = Core . Bound

lam :: String -> Term (Ann Surface ann) -> Term (Ann Surface ann)
lam n b = In (Ann (Core (Lam n b)) (ann (out b)))

(.:)  :: Semigroup ann => Term (Ann Surface ann) -> Term (Ann Surface ann) -> Term (Ann Surface ann)
a .: t = In (Ann (a ::: t) (ann (out a) <> ann (out t)))

(#) :: Semigroup ann => Term (Ann Surface ann) -> Term (Ann Surface ann) -> Term (Ann Surface ann)
f # a = In (Ann (Core (f :@ a)) (ann (out f) <> ann (out a)))


subst :: String -> Surface (Term (Ann Surface ann)) -> Term (Ann Surface ann) -> Term (Ann Surface ann)
subst i r (In (Ann (e ::: t) ann)) = In (Ann (subst i r e ::: subst i r t) ann)
subst i r (In (Ann (Core (Bound j)) ann))
  | i == j    = In (Ann r ann)
  | otherwise = In (Ann (Core (Bound j)) ann)
subst _ _ (In (Ann (Core (Free n)) ann)) = In (Ann (Core (Free n)) ann)
subst i r (In (Ann (Core (Lam n b)) ann))
  | i == n    = In (Ann (Core (Lam n b)) ann)
  | otherwise = In (Ann (Core (Lam n (subst i r b))) ann)
subst i r (In (Ann (Core (f :@ a)) ann)) = In (Ann (Core (subst i r f :@ subst i r a)) ann)
subst _ _ (In (Ann (Core Type) ann)) = In (Ann (Core Type) ann)
subst i r (In (Ann (Core (Pi n e t t')) ann))
  | i == n    = In (Ann (Core (Pi n e (subst i r t) t')) ann)
  | otherwise = In (Ann (Core (Pi n e (subst i r t) (subst i r t'))) ann)
