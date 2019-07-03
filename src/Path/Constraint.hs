{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeOperators #-}
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
import           Control.Monad (join)
import           Data.Bifunctor (first)
import           Data.Foldable (toList)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import           Path.Context
import           Path.Core (Core, prettyCore)
import           Path.Name
import           Path.Pretty
import           Path.Scope hiding (bind, instantiate, match)
import           Text.Trifecta.Rendering (Spanned (..))

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
  apply (Substitution subst) = bindConstraint (\ var -> fromMaybe (pure var) (name unMeta (const Nothing) var >>= (subst Map.!?)))


data Constraint a
  = Core a :|-: Constraint (Incr () (Core a))
  | E (Equation (Core a) ::: Core a)
  deriving (Eq, Ord, Show)

infixr 1 :|-:

instance Foldable Constraint where
  foldMap f (v :|-: s)    = foldMap f v <> foldMap (foldMap (foldMap f)) s
  foldMap f (E (q ::: t)) = foldMap (foldMap f) q <> foldMap f t

instance Functor Constraint where
  fmap f (v :|-: s)    = fmap f v :|-: fmap (fmap (fmap f)) s
  fmap f (E (q ::: t)) = E (fmap (fmap f) q ::: fmap f t)

instance Traversable Constraint where
  traverse f (v :|-: s)    = (:|-:) <$> traverse f v <*> traverse (traverse (traverse f)) s
  traverse f (E (q ::: t)) = fmap E . (:::) <$> traverse (traverse f) q <*> traverse f t

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
n ::: t |- b = t :|-: bind n b

infixr 1 |-

binds :: Context (Core (Name Meta)) -> Equation (Core (Name Meta)) ::: Core (Name Meta) -> Constraint (Name Meta)
binds (Context names) body = foldr (|-) (E body) (first (Local . Name) <$> names)

unbinds :: (Carrier sig m, Member Naming sig) => Constraint (Name Meta) -> m (Context (Core (Name Meta)), Equation (Core (Name Meta)) ::: Core (Name Meta))
unbinds = fmap (first Context) . un (\ name -> \case
  t :|-: b -> Right (name ::: t, instantiate (pure (Local (Name name))) b)
  E q      -> Left q)


efold :: forall m n a b
      .  (forall a . Core (m a) -> n (Incr () (Core (m a))) -> n a)
      -> (forall a . Equation (Core (m a)) ::: Core (m a) -> n a)
      -> (forall a . Incr () a -> m (Incr () a))
      -> (a -> m b)
      -> Constraint a
      -> n b
efold bind eqn k = go
  where go :: forall x y . (x -> m y) -> Constraint x -> n y
        go h = \case
          v :|-: b -> bind (h <$> v) (go (k . fmap (fmap h)) b)
          E (q ::: t) -> eqn ((fmap h <$> q) ::: (h <$> t))

bindConstraint :: (a -> Core b) -> Constraint a -> Constraint b
bindConstraint = efold
  (\ v s -> join v :|-: fmap (fmap join) s)
  (\ (q ::: t) -> E (fmap join q ::: join t))
  pure


-- | Bind occurrences of a name in a 'Constraint', producing a 'Scope' in which the name is bound.
bind :: Eq a => a -> Constraint a -> Constraint (Incr () (Core a))
bind name = fmap (match name)

-- | Substitute a 'Core' term for the free variable in a given 'Scope', producing a closed 'Constraint'.
instantiate :: Core a -> Constraint (Incr () (Core a)) -> Constraint a
instantiate t = bindConstraint (fromIncr (const t))

match :: (Applicative f, Eq a) => a -> a -> Incr () (f a)
match x y | x == y    = Z ()
          | otherwise = S (pure y)
