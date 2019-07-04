{-# LANGUAGE DeriveTraversable, DerivingVia, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}
module Path.Constraint
( Equation (..)
, Substitution
, Signature (..)
, Substitutable (..)
, Constraint (..)
, (|-)
, binds
, unbinds
) where

import           Control.Effect
import           Control.Monad (guard, join)
import           Control.Monad.Module
import           Data.Bifunctor (first)
import           Data.Bitraversable (bitraverse)
import           Data.Foldable (toList)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import           GHC.Generics ((:.:) (..))
import           Path.Context
import           Path.Core (Core, prettyCore)
import           Path.Name
import           Path.Pretty
import           Path.Scope hiding (bind, instantiate, match)
import           Path.Span

data Equation a
  = a :===: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 3 :===:

instance Pretty a => Pretty (Equation a) where
  pretty (t1 :===: t2) = flatAlt (pretty t1 <+> eq <+> pretty t2) (align (space <+> pretty t1 </> eq <+> pretty t2))
    where eq = magenta (pretty "≡")


type Substitution = Map.Map Gensym (Core (Name Meta))

newtype Signature = Signature { unSignature :: Map.Map Gensym (Core (Name Meta)) }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

instance Pretty Signature where
  pretty (Signature sig)
    | null sig  = mempty
    | otherwise = encloseSep (magenta (pretty "Σ") <> space) mempty (cyan comma <> space) (map (uncurry prettyBind) (Map.toList sig)) <> hardline
    where prettyBind m t = pretty (Meta m) <+> cyan colon <+> pretty t

class Substitutable t where
  apply :: Substitution -> t -> t

unMeta :: Meta -> Maybe Gensym
unMeta (Meta n) = Just n
unMeta _        = Nothing

instance Substitutable (Core (Name Meta)) where
  apply subst val = do
    var <- val
    fromMaybe (pure var) (name unMeta (const Nothing) var >>= (subst Map.!?))

instance Substitutable a => Substitutable (Equation a) where
  apply subst (s1 :===: s2) = apply subst s1 :===: apply subst s2

instance (Substitutable a, Substitutable b) => Substitutable (a ::: b) where
  apply subst (tm ::: ty) = apply subst tm ::: apply subst ty

instance (Ord a, Substitutable a) => Substitutable (Set.Set a) where
  apply subst = Set.map (apply subst)

instance Substitutable a => Substitutable (Spanned a) where
  apply subst (a :~ span) = apply subst a :~ span

instance Substitutable a => Substitutable (Context a) where
  apply subst = fmap (apply subst)

instance Substitutable (Constraint Core (Name Meta)) where
  apply subst = (>>=* \ var -> fromMaybe (pure var) (name unMeta (const Nothing) var >>= (subst Map.!?)))


data Constraint f a
  = f a :|-: ScopeH () (Constraint f) f a
  | E (Eqn f a)
  deriving (Foldable, Functor, Traversable)

infixr 1 :|-:

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Constraint f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Constraint f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (Constraint f a)

newtype Eqn f a = Eqn { unEqn :: Equation (f a) ::: f a }
  deriving (Eq, Ord, Show)
  deriving (Foldable, Functor) via (Comp2 (:::) (Equation :.: f) f)

instance Traversable f => Traversable (Eqn f) where
  traverse f  = fmap Eqn . bitraverse (traverse (traverse f)) (traverse f) . unEqn

instance Monad f => RModule (Constraint f) f where
  m >>=* f = efold (\ v s -> join v :|-: joinr s) (\ (q ::: t) -> E (Eqn (fmap join q ::: join t))) pure f m

instance Pretty (Constraint Core (Name Meta)) where
  pretty c = group . run . runNaming $ do
    (Context ctx, (v1 :===: v2) ::: t) <- unbinds c
    binds <- traverse prettyBind ctx
    v1' <- prettyCore v1
    v2' <- prettyCore v2
    t'  <- prettyCore t
    pure (cat (zipWith (<>) (l : repeat s) (toList binds) <> map (flatAlt mempty space <>) [ magenta (pretty "⊢") <+> prettyPrec 0 v1', magenta (pretty "≡") <+> prettyPrec 0 v2', cyan colon <+> prettyPrec 0 t' ]))
    where l = magenta (pretty "Γ") <> space
          s = softbreak <> cyan comma <> space
          prettyBind (n ::: t) = pretty . (Name n :::) . prettyPrec 0 <$> prettyCore t


(|-) :: (Applicative f, Eq a) => a ::: f a -> Constraint f a -> Constraint f a
n ::: t |- b = t :|-: bindH (guard . (== n)) b

infixr 1 |-

binds :: Applicative f => Context (f (Name Meta)) -> Equation (f (Name Meta)) ::: f (Name Meta) -> Constraint f (Name Meta)
binds (Context names) body = foldr (|-) (E (Eqn body)) (first (Local . Name) <$> names)

unbinds :: (Carrier sig m, Member Naming sig, Monad f) => Constraint f (Name Meta) -> m (Context (f (Name Meta)), Equation (f (Name Meta)) ::: f (Name Meta))
unbinds = fmap (first Context) . un (\ name -> \case
  t :|-: b  -> Right (name ::: t, instantiateH (const (pure (Local (Name name)))) b)
  E (Eqn q) -> Left q)


efold :: forall m n f a b
      .  Functor f
      => (forall a . f (m a) -> ScopeH () n f (m a) -> n a)
      -> (forall a . Equation (f (m a)) ::: f (m a) -> n a)
      -> (forall a . Incr () a -> m (Incr () a))
      -> (a -> m b)
      -> Constraint f a
      -> n b
efold bind eqn k = go
  where go :: forall x y . (x -> m y) -> Constraint f x -> n y
        go h = \case
          v :|-: b          -> bind (h <$> v) (ScopeH (go (k . fmap (fmap h)) (unScopeH b)))
          E (Eqn (q ::: t)) -> eqn ((fmap h <$> q) ::: (h <$> t))
