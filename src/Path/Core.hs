{-# LANGUAGE DataKinds, DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections, TypeApplications, TypeOperators #-}
module Path.Core where

import           Control.Applicative (Alternative (..))
import           Control.Effect.Carrier
import qualified Data.Set as Set
import           GHC.Generics (Generic1)
import           Path.Fin
import           Path.Nat
import           Path.Pretty
import           Path.Scope
import           Path.Syntax
import           Path.Vec
import           Prelude hiding (pi)
import           Syntax.Module
import           Syntax.Scope
import           Syntax.Sum
import           Syntax.Term
import           Syntax.Var

data Core f a
  = Lam (Scope () f a)
  | f a :$ f a
  | Let (f a) (Scope () f a)
  | Type
  | Pi (f a) (Scope () f a)
  deriving (Foldable, Functor, Generic1, HFunctor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Core f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Core f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (Core f a)

instance RightModule Core where
  Lam b   >>=* f = Lam (b >>=* f)
  g :$ a  >>=* f = (g >>= f) :$ (a >>= f)
  Let v b >>=* f = Let (v >>= f) (b >>=* f)
  Type    >>=* _ = Type
  Pi t b  >>=* f = Pi (t >>= f) (b >>=* f)


lam :: (Eq a, Carrier sig m, Member Core sig) => a -> m a -> m a
lam n b = send (Lam (abstract1 n b))

lamFin :: (Carrier sig m, Member Core sig) => m (Var (Fin ('S n)) a) -> m (Var (Fin n) a)
lamFin b = send (Lam (toScopeFin b))

lams :: (Eq a, Foldable t, Carrier sig m, Member Core sig) => t a -> m a -> m a
lams names body = foldr lam body names

unlam :: (Alternative m, Project Core sig, RightModule sig) => a -> Term sig a -> m (a, Term sig a)
unlam n t | Just (Lam b) <- prjTerm t = pure (n, instantiate1 (pure n) b)
unlam _ _                             = empty

unlamFin :: (Alternative m, Project Core sig, RightModule sig) => Term sig (Var (Fin n) a) -> m (Term sig (Var (Fin ('S n)) a))
unlamFin t | Just (Lam b) <- prjTerm t = pure (fromScopeFin b)
unlamFin _                             = empty


($$) :: (Carrier sig m, Member Core sig) => m a -> m a -> m a
f $$ a = send (f :$ a)

unapply :: (Alternative m, Project Core sig) => Term sig a -> m (Term sig a, Term sig a)
unapply t | Just (f :$ a) <- prjTerm t = pure (f, a)
unapply _                              = empty


let' :: (Eq a, Carrier sig m, Member Core sig) => a := m a -> m a -> m a
let' (n := v) b = send (Let v (abstract1 n b))

letFin :: (Carrier sig m, Member Core sig) => m (Var (Fin n) a) -> m (Var (Fin ('S n)) a) -> m (Var (Fin n) a)
letFin v b = send (Let v (toScopeFin b))

unlet' :: (Alternative m, Project Core sig, RightModule sig) => a -> Term sig a -> m (a := Term sig a, Term sig a)
unlet' n t | Just (Let v b) <- prjTerm t = pure (n := v, instantiate1 (pure n) b)
unlet' _ _                               = empty

unletFin :: (Alternative m, Project Core sig, RightModule sig) => Term sig (Var (Fin n) a) -> m (Term sig (Var (Fin n) a), Term sig (Var (Fin ('S n)) a))
unletFin t | Just (Let v b) <- prjTerm t = pure (v, fromScopeFin b)
unletFin _                               = empty


type' :: (Carrier sig m, Member Core sig) => m a
type' = send Type

pi :: (Eq a, Carrier sig m, Member Core sig) => a ::: m a -> m a -> m a
pi (n ::: t) b = send (Pi t (abstract1 n b))

piFin :: (Carrier sig m, Member Core sig) => m (Var (Fin n) a) -> m (Var (Fin ('S n)) a) -> m (Var (Fin n) a)
piFin t b = send (Pi t (toScopeFin b))

-- | Wrap a type in a sequence of pi abstractings.
pis :: (Eq a, Foldable t, Carrier sig m, Member Core sig) => t (a ::: m a) -> m a -> m a
pis names body = foldr pi body names

unpi :: (Alternative m, Project Core sig, RightModule sig) => a -> Term sig a -> m (a ::: Term sig a, Term sig a)
unpi n t | Just (Pi t b) <- prjTerm t = pure (n ::: t, instantiate1 (pure n) b)
unpi _ _                              = empty

unpiFin :: (Alternative m, Project Core sig, RightModule sig) => Term sig (Var (Fin n) a) -> m (Term sig (Var (Fin n) a), Term sig (Var (Fin ('S n)) a))
unpiFin t | Just (Pi t b) <- prjTerm t = pure (t, fromScopeFin b)
unpiFin _                              = empty


instance Pretty a => Pretty (Term Core a) where
  pretty = prettyTerm pretty prettyCore

prettyCore
  :: (Foldable f, Monad f)
  => (forall n . Vec n Doc -> f (Var (Fin n) a) -> Prec Doc)
  -> Vec n Doc
  -> Core f (Var (Fin n) a)
  -> Prec Doc
prettyCore go ctx = \case
  Lam b ->
    let n  = prettyVar (length ctx)
        b' = withPrec 0 (go (n :# ctx) (fromScopeFin b))
    in prec 0 (group (vsep [cyan backslash <+> n, cyan dot <+> b']))
  f :$ a ->
    let f' = withPrec 10 (go ctx f)
        a' = withPrec 11 (go ctx a)
    in prec 10 (f' <+> a')
  Let v b ->
    let v' = withPrec 0 (go ctx v)
        n  = prettyVar (length ctx)
        b' = withPrec 0 (go (n :# ctx) (fromScopeFin b))
    in prec 0 (group (vsep [magenta (pretty "let") <+> pretty (n := v'), magenta dot <+> b']))
  Type -> atom (yellow (pretty "Type"))
  Pi t b ->
    let t'  = withPrec 1 (go ctx t)
        n   = prettyVar (length ctx)
        b'  = fromScopeFin b
        fvs = foldMap (unVar Set.singleton (const Set.empty)) b'
        b'' = withPrec 0 (go (n :# ctx) b')
        t'' | FZ `Set.member` fvs = parens (pretty (n ::: t'))
            | otherwise           = t'
    in prec 0 (group (vsep [t'', arrow <+> b'']))
  where arrow = blue (pretty "→")


-- $setup
-- >>> import Test.QuickCheck
