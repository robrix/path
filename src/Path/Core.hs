{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections, TypeApplications, TypeOperators #-}
module Path.Core where

import           Control.Applicative (Alternative (..))
import           Control.Effect.Carrier
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.Writer
import           Control.Monad.Module
import qualified Data.Set as Set
import           GHC.Generics (Generic1)
import           Path.Name
import           Path.Pretty
import           Path.Scope
import           Path.Syntax
import           Path.Term
import           Prelude hiding (pi)

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
lam n b = send (Lam (bind1 n b))

lams :: (Eq a, Foldable t, Carrier sig m, Member Core sig) => t a -> m a -> m a
lams names body = foldr lam body names

unlam :: (Alternative m, Member Core sig, RightModule sig) => a -> Term sig a -> m (a, Term sig a)
unlam n (Term t) | Just (Lam b) <- prj t = pure (n, instantiate1 (pure n) b)
unlam _ _                                = empty

($$) :: (Carrier sig m, Member Core sig) => m a -> m a -> m a
f $$ a = send (f :$ a)


let' :: (Eq a, Carrier sig m, Member Core sig) => a := m a -> m a -> m a
let' (n := v) b = send (Let v (bind1 n b))

unlet' :: (Alternative m, Member Core sig, RightModule sig) => a -> Term sig a -> m (a := Term sig a, Term sig a)
unlet' n (Term t) | Just (Let v b) <- prj t = pure (n := v, instantiate1 (pure n) b)
unlet' _ _                                  = empty


type' :: (Carrier sig m, Member Core sig) => m a
type' = send Type

pi :: (Eq a, Carrier sig m, Member Core sig) => a ::: m a -> m a -> m a
pi (n ::: t) b = send (Pi t (bind1 n b))

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t, Carrier sig m, Member Core sig) => t (a ::: m a) -> m a -> m a
pis names body = foldr pi body names

unpi :: (Alternative m, Member Core sig, RightModule sig) => a -> Term sig a -> m (a ::: Term sig a, Term sig a)
unpi n (Term t) | Just (Pi t b) <- prj t = pure (n ::: t, instantiate1 (pure n) b)
unpi _ _                                 = empty


generalizeType :: Ord n => Term Core (Name n) -> Term Core Qualified
generalizeType ty = name undefined id <$> uncurry pis (traverse (traverse f) ty)
  where f name = (Set.singleton (Local name ::: type'), name)


instance Pretty a => Pretty (Term Core a) where
  pretty = prettyTerm prettyCore

prettyCore :: (Carrier sig m, Member (Reader N) sig, Member (Writer (Set.Set N)) sig, Monad f) => (f (m Prec) -> m Prec) -> Core f (m Prec) -> m Prec
prettyCore go = \case
  Lam b -> do
    (n, b') <- binding go pretty b
    pure (prec 0 (pretty (cyan backslash) <+> pretty n </> cyan dot <+> withPrec 0 b'))
  f :$ a -> do
    f' <- withPrec 10 <$> go f
    a' <- withPrec 11 <$> go a
    pure (prec 10 (f' <+> a'))
  Let v b -> do
    v' <- withPrec 0 <$> go v
    (n, b') <- binding go prettyMeta b
    pure (prec 0 (magenta (pretty "let") <+> pretty (n := v') </> magenta dot <+> withPrec 0 b'))
  Type -> pure (atom (yellow (pretty "Type")))
  Pi t b -> do
    t' <- withPrec 1 <$> go t
    (fvs, (n, b')) <- listen (binding go pretty b)
    let t'' | n `Set.member` fvs = parens (pretty (n ::: t'))
            | otherwise          = t'
    pure (prec 0 (t'' </> arrow <+> withPrec 0 b'))
  where arrow = blue (pretty "→")


-- $setup
-- >>> import Test.QuickCheck
