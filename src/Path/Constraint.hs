{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Constraint where

import Control.Effect
import Control.Monad (join)
import Data.Bifunctor (first)
import Data.Foldable (toList)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Path.Context
import Path.Name
import Path.Pretty
import Path.Value (Value, Type, prettyValue)
import Text.Trifecta.Rendering (Spanned(..))

data Equation a
  = a :===: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 3 :===:

instance Pretty a => Pretty (Equation a) where
  pretty (t1 :===: t2) = flatAlt (pretty t1 <+> eq <+> pretty t2) (align (space <+> pretty t1 </> eq <+> pretty t2))
    where eq = magenta (pretty "≡")

instance FreeVariables v a => FreeVariables v (Equation a) where
  fvs (a1 :===: a2) = fvs a1 <> fvs a2


newtype Substitution = Substitution { unSubstitution :: Map.Map Gensym (Value Meta) }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

instance Pretty Substitution where
  pretty (Substitution sig)
    | null sig  = mempty
    | otherwise = encloseSep (magenta (pretty "Θ") <> space) mempty (cyan comma <> space) (map (uncurry prettyBind) (Map.toList sig)) <> hardline
    where prettyBind m t = pretty (Meta m) <+> cyan (pretty "=") <+> pretty t

newtype Signature = Signature { unSignature :: Map.Map Gensym (Value Meta) }
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

instance Substitutable (Value Meta) where
  apply (Substitution subst) val = do
    var <- val
    fromMaybe (pure var) (unMeta var >>= (subst Map.!?))

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

instance Substitutable (Constraint Meta) where
  apply (Substitution subst) = joinT . fmap (\ var -> fromMaybe (pure var) (unMeta var >>= (subst Map.!?)))


data Constraint a
  = Value a :|-: Constraint (Incr a)
  | E (Equation (Value a) ::: Type a)
  deriving (Eq, Ord, Show)

infixr 1 :|-:

instance Foldable Constraint where
  foldMap f (v :|-: s) = foldMap f v <> foldMap (foldMap f) s
  foldMap f (E (q ::: t)) = foldMap (foldMap f) q <> foldMap f t

instance Functor Constraint where
  fmap f (v :|-: s) = fmap f v :|-: fmap (fmap f) s
  fmap f (E (q ::: t)) = E (fmap (fmap f) q ::: fmap f t)

instance Traversable Constraint where
  traverse f (v :|-: s) = (:|-:) <$> traverse f v <*> traverse (traverse f) s
  traverse f (E (q ::: t)) = fmap E . (:::) <$> traverse (traverse f) q <*> traverse f t

instance Ord a => FreeVariables a (Constraint a) where
  fvs = foldMap Set.singleton

instance Pretty (Constraint Meta) where
  pretty c = group . run . runNaming (Root "pretty") $ do
    (Context ctx, (v1 :===: v2) ::: t) <- unbinds c
    binds <- traverse prettyBind ctx
    v1' <- prettyValue v1
    v2' <- prettyValue v2
    t'  <- prettyValue t
    pure (cat (zipWith (<>) (l : repeat s) (toList binds) <> map (flatAlt mempty space <>) [ magenta (pretty "⊢") <+> prettyPrec 0 v1', magenta (pretty "≡") <+> prettyPrec 0 v2', cyan colon <+> prettyPrec 0 t' ]))
    where l = magenta (pretty "Γ") <> space
          s = softbreak <> cyan comma <> space
          prettyBind (n ::: t) = pretty . (Name n :::) . prettyPrec 0 <$> prettyValue t


(|-) :: Eq a => a ::: Type a -> Constraint a -> Constraint a
n ::: t |- b = t :|-: bind n b

infixr 1 |-

binds :: Context (Type Meta) -> Equation (Value Meta) ::: Type Meta -> Constraint Meta
binds (Context names) body = foldr (|-) (E body) (first Name <$> names)

unbinds :: (Carrier sig m, Member Naming sig) => Constraint Meta -> m (Context (Type Meta), Equation (Value Meta) ::: Type Meta)
unbinds = fmap (first Context) . un (\ name -> \case
  t :|-: b -> Right (name ::: t, instantiate (pure (Name name)) b)
  E q      -> Left q)


gfoldT :: forall m n b
       .  (forall a . Value (m a) -> n (Incr a) -> n a)
       -> (forall a . Equation (Value (m a)) ::: Type (m a) -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Constraint (m b)
       -> n b
gfoldT bind eqn dist = go
  where go :: Constraint (m x) -> n x
        go (v :|-: b) = bind v (go (dist <$> b))
        go (E a)      = eqn a

joinT :: Constraint (Value a) -> Constraint a
joinT = gfoldT
  (\ v s -> join v :|-: s)
  (\ (q ::: t) -> E (fmap join q ::: join t))
  (incr (pure Z) (fmap S))


-- | Bind occurrences of a name in a 'Constraint', producing a 'Scope' in which the name is bound.
bind :: Eq a => a -> Constraint a -> Constraint (Incr a)
bind name = fmap (match name)

-- | Substitute a 'Value' term for the free variable in a given 'Scope', producing a closed 'Constraint'.
instantiate :: Value a -> Constraint (Incr a) -> Constraint a
instantiate t b = joinT (subst t . fmap pure <$> b)
