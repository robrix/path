{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections, TypeApplications, TypeOperators #-}
module Path.Core where

import           Control.Applicative (Alternative (..))
import           Control.Effect.Carrier
import           Control.Monad.Module
import qualified Data.Set as Set
import           GHC.Generics (Generic1)
import           Path.Name
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

instance HRModule Core where
  Lam b   >>=** f = Lam (b >>=** f)
  g :$ a  >>=** f = (g >>= f) :$ (a >>= f)
  Let v b >>=** f = Let (v >>= f) (b >>=** f)
  Type    >>=** _ = Type
  Pi t b  >>=** f = Pi (t >>= f) (b >>=** f)

instance Syntax Core where
  foldSyntax go bound free = \case
    Lam b -> Lam (foldSyntax go bound free b)
    f :$ a -> go free f :$ go free a
    Let v b -> Let (go free v) (foldSyntax go bound free b)
    Type -> Type
    Pi t b -> Pi (go free t) (foldSyntax go bound free b)


lam :: (Eq a, Carrier sig m, Member Core sig) => a -> m a -> m a
lam n b = send (Lam (bind1 n b))

lams :: (Eq a, Foldable t, Carrier sig m, Member Core sig) => t a -> m a -> m a
lams names body = foldr lam body names

unlam :: (Alternative m, Member Core sig, HRModule sig) => a -> Term sig a -> m (a, Term sig a)
unlam n (Term t) | Just (Lam b) <- prj t = pure (n, instantiate1 (pure n) b)
unlam _ _                                = empty

($$) :: (Carrier sig m, Member Core sig) => m a -> m a -> m a
f $$ a = send (f :$ a)


let' :: (Eq a, Carrier sig m, Member Core sig) => a := m a -> m a -> m a
let' (n := v) b = send (Let v (bind1 n b))

unlet' :: (Alternative m, Member Core sig, HRModule sig) => a -> Term sig a -> m (a := Term sig a, Term sig a)
unlet' n (Term t) | Just (Let v b) <- prj t = pure (n := v, instantiate1 (pure n) b)
unlet' _ _                                  = empty


type' :: (Carrier sig m, Member Core sig) => m a
type' = send Type

pi :: (Eq a, Carrier sig m, Member Core sig) => a ::: m a -> m a -> m a
pi (n ::: t) b = send (Pi t (bind1 n b))

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t, Carrier sig m, Member Core sig) => t (a ::: m a) -> m a -> m a
pis names body = foldr pi body names

unpi :: (Alternative m, Member Core sig, HRModule sig) => a -> Term sig a -> m (a ::: Term sig a, Term sig a)
unpi n (Term t) | Just (Pi t b) <- prj t = pure (n ::: t, instantiate1 (pure n) b)
unpi _ _                                 = empty


generalizeType :: Term Core (Name Meta) -> Term Core Qualified
generalizeType ty = name undefined id <$> uncurry pis (traverse (traverse f) ty)
  where f v = let name = case v of { Name n -> n ; Meta n -> n } in (Set.singleton (Local name ::: type'), name)


-- $setup
-- >>> import Test.QuickCheck
