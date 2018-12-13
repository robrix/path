{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Control.Effect
import Control.Effect.Fresh
import Control.Effect.Reader
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Pretty
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen

data Term f a = In { out :: f (Term f a), ann :: a }

deriving instance (Eq   (f (Term f a)), Eq   a) => Eq   (Term f a)
deriving instance (Ord  (f (Term f a)), Ord  a) => Ord  (Term f a)
deriving instance (Show (f (Term f a)), Show a) => Show (Term f a)

instance (PrettyPrec (f (Term f a)), PrettyPrec a) => PrettyPrec (Term f a) where
  prettyPrec d (In tm ty)
    | show ty' == "" = prettyPrec d tm
    | otherwise      = prettyParens (d > 0) $ prettyPrec 1 tm <> pretty " : " <> ty'
    where ty' = prettyPrec 1 ty

instance (PrettyPrec (f (Term f a)), PrettyPrec a) => Pretty (Term f a) where
  pretty = prettyPrec 0

instance Functor f => Functor (Term f) where
  fmap f (In tm a) = In (fmap (fmap f) tm) (f a)

cata :: Functor f => (f b -> a -> b) -> Term f a -> b
cata alg = go where go = alg . fmap go . out <*> ann

hoist :: Functor f => (forall x . f x -> g x) -> Term f a -> Term g a
hoist f = cata (In . f)


class Ord v => AlphaEquivalent v a | a -> v where
  aeq :: (Carrier sig m, Member Fresh sig, Member (Reader (Map.Map v Int)) sig) => a -> a -> m Bool

class Ord v => AlphaEquivalent1 v t | t -> v where
  liftAeq :: (Carrier sig m, Member Fresh sig, Member (Reader (Map.Map v Int)) sig) => (a -> b -> m Bool) -> t a -> t b -> m Bool

instance AlphaEquivalent1 v f => AlphaEquivalent v (Term f a) where
  aeq (In syn1 _) (In syn2 _) = liftAeq aeq syn1 syn2

aeqLookup :: (Carrier sig m, Functor m, Member (Reader (Map.Map v Int)) sig, Ord v) => v -> m (Maybe Int)
aeqLookup = asks . Map.lookup

aeqBind ::  (Carrier sig m, Member Fresh sig, Member (Reader (Map.Map v Int)) sig, Monad m, Ord v) => Maybe v -> Maybe v -> m a -> m a
aeqBind v1 v2 m
  | v1 == v2  = m
  | otherwise = do
    i <- fresh
    local (insert v1 i . insert v2 i) m
  where insert (Just v) = Map.insert v
        insert _        = flip const


class Ord v => FreeVariables v a where
  fvs :: a -> Set.Set v

class Ord v => FreeVariables1 v t where
  liftFvs :: (a -> Set.Set v) -> t a -> Set.Set v

instance (FreeVariables1 v f, FreeVariables v a) => FreeVariables v (Term f a) where
  fvs (In out ann) = liftFvs fvs out <> fvs ann

instance Ord v => FreeVariables v () where
  fvs _ = Set.empty

instance (FreeVariables v a, FreeVariables v b) => FreeVariables v (a, b) where
  fvs (a, b) = fvs a <> fvs b

instance (FreeVariables v key, FreeVariables v value) => FreeVariables v (Map.Map key value) where
  fvs = fvs . Map.toList

instance FreeVariables v a => FreeVariables v [a] where
  fvs = foldMap fvs

instance Ord v => FreeVariables v v where
  fvs = Set.singleton

instance Ord v => FreeVariables v (Set.Set v) where
  fvs = id

instance Ord v => FreeVariables v Usage where
  fvs _ = Set.empty
