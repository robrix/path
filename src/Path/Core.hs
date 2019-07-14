{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections, TypeApplications, TypeOperators #-}
module Path.Core where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Carrier
import           Data.Foldable (foldl')
import qualified Data.Set as Set
import           GHC.Generics (Generic1)
import           Path.Name
import           Path.Plicity
import           Path.Scope
import           Path.Stack as Stack
import           Path.Term
import           Path.Usage
import           Prelude hiding (pi)

data Core f a
  = Lam Plicity (Scope () f a)              -- ^ A lambda abstraction.
  | f a :$ Stack (Plicit (f a))             -- ^ A neutral term represented as a function and a 'Stack' of arguments to apply it to.
  | Type                                    -- ^ @'Type' : 'Type'@.
  | Pi (Plicit (Used (f a))) (Scope () f a) -- ^ A ∏ type, with a 'Usage' annotation.
  deriving (Foldable, Functor, Generic1, HFunctor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Core f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Core f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (Core f a)

instance Syntax Core where
  foldSyntax go bound free = \case
    Lam p b -> Lam p (foldSyntax go bound free b)
    f :$ a -> go free f :$ (fmap (go free) <$> a)
    Type -> Type
    Pi t b -> Pi (fmap (go free) <$> t) (foldSyntax go bound free b)

lam :: (Eq a, Carrier sig m, Member Core sig) => Plicit a -> m a -> m a
lam (pl :< n) b = send (Lam pl (bind1 n b))

lams :: (Eq a, Foldable t, Carrier sig m, Member Core sig) => t (Plicit a) -> m a -> m a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Term Core a -> m (Plicit a, Term Core a)
unlam n (Term (Lam p b)) = pure (p :< n, instantiate1 (pure n) b)
unlam _ _                = empty

($$) :: (Carrier sig m, Member Core sig) => m a -> Plicit (m a) -> m a
a $$ b = a $$* (Nil :> b)

($$*) :: (Foldable t, Carrier sig m, Member Core sig) => m a -> t (Plicit (m a)) -> m a
v $$* sp = send (v :$ foldl' (:>) Nil sp)

type' :: (Carrier sig m, Member Core sig) => m a
type' = send Type

pi :: (Eq a, Carrier sig m, Member Core sig) => Plicit (a ::: Used (m a)) -> m a -> m a
pi (p :< n ::: t) b = send (Pi (p :< t) (bind1 n b))

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t, Carrier sig m, Member Core sig) => t (Plicit (a ::: Used (m a))) -> m a -> m a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Term Core a -> m (Plicit (a ::: Used (Term Core a)), Term Core a)
unpi n (Term (Pi (p :< t) b)) = pure (p :< n ::: t, instantiate1 (pure n) b)
unpi _ _                      = empty


generalizeType :: Term Core (Name Meta) -> Term Core Qualified
generalizeType ty = name undefined id <$> uncurry pis (traverse (traverse f) ty)
  where f v = let name = case v of { Name n -> n ; Meta n -> n } in (Set.singleton (Im :< Local name ::: Zero :@ type'), name)


-- $setup
-- >>> import Test.QuickCheck
