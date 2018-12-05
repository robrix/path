{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Path.Surface where

import Data.Function (fix)
import Path.Expr
import qualified Data.Set as Set

data Surface a
  = Core (Core a)
  | Ann a a
  deriving (Eq, Functor, Ord, Show)

(-->) :: (String, Plicity, Term Surface) -> Term Surface -> Term Surface
(n, e, a) --> b = Term (Core (Pi n e a b))

infixr 0 -->

typeT :: Term Surface
typeT = Term (Core Type)

global :: String -> Term Surface
global = Term . Core . Free . Global

var :: String -> Term Surface
var = Term . Core . Bound

lam :: String -> Term Surface -> Term Surface
lam n = Term . Core . Lam n

(.:)  :: Term Surface -> Term Surface -> Term Surface
a .: t = Term (Ann a t)

(#) :: Term Surface -> Term Surface -> Term Surface
f # a = Term (Core (f :@ a))


surfaceFVs :: Surface (Set.Set Name) -> Set.Set Name
surfaceFVs (Core core) = coreFVs core
surfaceFVs (Ann tm ty) = tm <> ty


instance Show (Term Surface) where
  showsPrec = fix (\ f d (Term surface) -> case surface of
    Core core -> showCore f (cata surfaceFVs) d core
    Ann e t -> showParen (d > 0) $ f 1 e . showString " : " . f 0 t)


subst :: String -> Term Surface -> Term Surface -> Term Surface
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


identity :: Term Surface
identity = lam "0" (var "0")

constant :: Term Surface
constant = lam "1" (lam "0" (var "1"))
