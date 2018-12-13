{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Path.Surface where

import Data.Bifunctor
import Path.Core
import Path.FreeVariables
import Path.Name
import Path.Pretty
import Path.Semiring
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Surface v a
  = Core (Core v a)
  | a ::: a
  deriving (Eq, Functor, Ord, Show)

instance Bifunctor Surface where
  bimap f g (Core core) = Core (bimap f g core)
  bimap _ g (a ::: t) = g a ::: g t

instance (FreeVariables a, PrettyPrec a) => PrettyPrec (Surface Name a) where
  prettyPrec d (Core core) = prettyPrec d core
  prettyPrec d (tm ::: ty) = prettyParens (d > 0) $ prettyPrec 1 tm <+> pretty ":" <+> prettyPrec 0 ty

instance FreeVariables1 (Surface Name) where
  liftFvs fvs (Core core) = liftFvs fvs core
  liftFvs fvs (tm ::: ty) = fvs tm <> fvs ty

instance FreeVariables a => FreeVariables (Surface Name a) where
  fvs = fvs1

(-->) :: Semigroup ann => (Maybe String, Usage, Term (Surface Name) ann) -> Term (Surface Name) ann -> Term (Surface Name) ann
(n, e, a) --> b = In (Core (Pi (Local <$> n) e a b)) (ann a <> ann b)

infixr 0 -->

forAll :: Semigroup ann => (Maybe String, Term (Surface Name) ann) -> Term (Surface Name) ann -> Term (Surface Name) ann
forAll (n, a) b = (n, zero, a) --> b

typeT :: Surface Name a
typeT = Core Type

var :: String -> Surface Name a
var = Core . Var . Local

lam :: Semigroup ann => (Maybe String, ann) -> Term (Surface Name) ann -> Term (Surface Name) ann
lam (n, a) b = In (Core (Lam (Local <$> n) b)) (a <> ann b)

(.:)  :: Semigroup ann => Term (Surface Name) ann -> Term (Surface Name) ann -> Term (Surface Name) ann
a .: t = In (a ::: t) (ann a <> ann t)

(#) :: Semigroup ann => Term (Surface Name) ann -> Term (Surface Name) ann -> Term (Surface Name) ann
f # a = In (Core (f :@ a)) (ann f <> ann a)


subst :: Name -> Surface Name (Term (Surface Name) ann) -> Term (Surface Name) ann -> Term (Surface Name) ann
subst i r (In (e ::: t) ann) = In (subst i r e ::: subst i r t) ann
subst i r (In (Core (Var j)) ann)
  | i == j    = In r ann
  | otherwise = In (Core (Var j)) ann
subst i r (In (Core (Lam n b)) ann)
  | Just i == n = In (Core (Lam n b)) ann
  | otherwise   = In (Core (Lam n (subst i r b))) ann
subst i r (In (Core (f :@ a)) ann) = In (Core (subst i r f :@ subst i r a)) ann
subst _ _ (In (Core Type) ann) = In (Core Type) ann
subst i r (In (Core (Pi n e t t')) ann)
  | Just i == n = In (Core (Pi n e (subst i r t) t')) ann
  | otherwise   = In (Core (Pi n e (subst i r t) (subst i r t'))) ann


uses :: Name -> Term (Surface Name) a -> [a]
uses n = cata $ \ f a -> case f of
  Core (Var n')
    | n == n'   -> [a]
    | otherwise -> []
  Core (Lam n' b)
    | Just n == n' -> []
    | otherwise    -> b
  Core (f :@ a) -> f <> a
  Core Type -> []
  Core (Pi n' _ t b)
    | Just n == n' -> t
    | otherwise    -> t <> b
  a ::: t -> a <> t
