{-# LANGUAGE DeriveTraversable, DerivingVia, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Constraint
( Equation (..)
, Substitution (..)
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


newtype Substitution = Substitution { unSubstitution :: Map.Map Gensym (Core (Name Meta)) }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

instance Pretty Substitution where
  pretty (Substitution sig)
    | null sig  = mempty
    | otherwise = encloseSep (magenta (pretty "Θ") <> space) mempty (cyan comma <> space) (map (uncurry prettyBind) (Map.toList sig)) <> hardline
    where prettyBind m t = pretty (Meta m) <+> cyan (pretty "=") <+> pretty t

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
  apply (Substitution subst) val = do
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

instance Substitutable (Constraint (Name Meta)) where
  apply (Substitution subst) = (>>=* \ var -> fromMaybe (pure var) (name unMeta (const Nothing) var >>= (subst Map.!?)))


data Constraint a
  = Core a :|-: ScopeH () Constraint Core a
  | E (Eqn a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 1 :|-:

newtype Eqn a = Eqn { unEqn :: Equation (Core a) ::: Core a }
  deriving (Eq, Ord, Show)
  deriving (Foldable, Functor) via (Comp2 (:::) (Equation :.: Core) Core)

instance Traversable Eqn where
  traverse f  = fmap Eqn . bitraverse (traverse (traverse f)) (traverse f) . unEqn

instance RModule Constraint Core where
  m >>=* f = efold (\ v s -> join v :|-: joinr s) (\ (q ::: t) -> E (Eqn (fmap join q ::: join t))) pure f m

instance Pretty (Constraint (Name Meta)) where
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


(|-) :: Eq a => a ::: Core a -> Constraint a -> Constraint a
n ::: t |- b = t :|-: bindH (guard . (== n)) b

infixr 1 |-

binds :: Context (Core (Name Meta)) -> Equation (Core (Name Meta)) ::: Core (Name Meta) -> Constraint (Name Meta)
binds (Context names) body = foldr (|-) (E (Eqn body)) (first (Local . Name) <$> names)

unbinds :: (Carrier sig m, Member Naming sig) => Constraint (Name Meta) -> m (Context (Core (Name Meta)), Equation (Core (Name Meta)) ::: Core (Name Meta))
unbinds = fmap (first Context) . un (\ name -> \case
  t :|-: b  -> Right (name ::: t, instantiateH (const (pure (Local (Name name)))) b)
  E (Eqn q) -> Left q)


efold :: forall m n a b
      .  (forall a . Core (m a) -> ScopeH () n Core (m a) -> n a)
      -> (forall a . Equation (Core (m a)) ::: Core (m a) -> n a)
      -> (forall a . Incr () a -> m (Incr () a))
      -> (a -> m b)
      -> Constraint a
      -> n b
efold bind eqn k = go
  where go :: forall x y . (x -> m y) -> Constraint x -> n y
        go h = \case
          v :|-: b          -> bind (h <$> v) (ScopeH (go (k . fmap (fmap h)) (unScopeH b)))
          E (Eqn (q ::: t)) -> eqn ((fmap h <$> q) ::: (h <$> t))
