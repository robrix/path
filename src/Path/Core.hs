{-# LANGUAGE DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections, TypeApplications, TypeOperators #-}
module Path.Core where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.Reader hiding (Local)
import           Data.Foldable (foldl', toList)
import qualified Data.Set as Set
import           GHC.Generics (Generic1)
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Scope
import           Path.Span (Span)
import           Path.Stack as Stack
import           Path.Usage
import           Prelude hiding (pi)

data Core a
  = Lam Plicity (Scope () Core a)                 -- ^ A lambda abstraction.
  | a :$ Stack (Plicit (Core a))                  -- ^ A neutral term represented as a function and a 'Stack' of arguments to apply it to.
  | Type                                          -- ^ @'Type' : 'Type'@.
  | Pi (Plicit (Used (Core a))) (Scope () Core a) -- ^ A ∏ type, with a 'Usage' annotation.
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

prettyCore :: (Carrier sig m, Member Naming sig) => Core (Name Meta) -> m (Prec Doc)
prettyCore = \case
  Lam ie b -> do
    (as, b') <- un (\case
      Lam p b -> Just $ do
        n <- fresh
        pure (p :< Local (Name n), instantiate1 (pure (Local (Name n))) b)
      _ -> Nothing) (Lam ie b)
    b'' <- prettyCore b'
    pure (prec 0 (align (group (cyan backslash <+> foldr (var (fvs b')) (linebreak <> cyan dot <+> prettyPrec 0 b'') as))))
    where var vs (p :< n) rest
            | n `Set.member` vs = prettyPlicity False (p :< pretty (Local n)) <+> rest
            | otherwise         = prettyPlicity False (p :< pretty '_')       <+> rest
  f :$ Nil -> pure (atom (pretty f))
  f :$ sp -> do
    sp' <- traverse prettyArg (toList sp)
    pure (prec 10 (hsep (pretty f : sp')))
    where prettyArg (Im :< a) = prettyBraces True . prettyPrec 0 <$> prettyCore a
          prettyArg (Ex :< a) = prettyPrec 11 <$> prettyCore a
  Type -> pure (atom (yellow (pretty "Type")))
  v@Pi{} -> do
    (pis, body) <- un (\case
      Pi (p :< u :@ t) b -> Just $ do
        n <- fresh
        let b' = instantiate1 (pure (Local (Name n))) b
        pure ((p :< Local (Name n) ::: u :@ t, Local (Name n) `Set.member` fvs b'), b')
      _                  -> Nothing) v
    pis' <- traverse (uncurry prettyPi) pis
    body' <- prettyCore body
    pure (prec 0 (encloseSep l mempty (flatAlt mempty space <> arrow <> space) (toList (pis' :> prettyPrec 1 body'))))
    where withPi (Ex :< More :@ t) =                   prettyPrec 1  <$> prettyCore t
          withPi (Im :< Zero :@ t) =                   prettyPrec 1  <$> prettyCore t
          withPi (_  :< pi   :@ t) = (pretty pi <+>) . prettyPrec 11 <$> prettyCore t
          arrow = blue (pretty "->")
          l = flatAlt (space <> space <> space) mempty
          prettyPi (p :< n ::: t) isUsed = do
            t' <- withPi (p :< t)
            pure $! prettyPlicity isUsed (p :< if isUsed then pretty (Local n ::: t') else t')

instance Pretty (Core (Name Meta)) where
  pretty = prettyPrec 0 . run . runNaming . prettyCore

instance Pretty (Core (Name Gensym)) where
  pretty = pretty . fmap (fmap Name)

instance Pretty (Core Qualified) where
  pretty = pretty @(Core (Name Meta)) . fmap Global

instance Applicative Core where
  pure = (:$ Nil)
  f <*> a = eiter id embed pure (<$> a) f

instance Monad Core where
  a >>= f = eiter id embed pure f a


data CoreF v f a
  = LamF Plicity (Scope v f a)              -- ^ A lambda abstraction.
  | f a :$$ Stack (Plicit (f a))            -- ^ A neutral term represented as a function and a 'Stack' of arguments to apply it to.
  | TypeF                                   -- ^ @'Type' : 'Type'@.
  | PiF (Plicit (Used (f a))) (Scope v f a) -- ^ A ∏ type, with a 'Usage' annotation.
  deriving (Foldable, Functor, Generic1, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (CoreF () f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (CoreF () f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (CoreF () f a)

project :: Core a -> CoreF () Core a
project (Lam p b) = LamF p b
project (f :$ a) = (f :$ Nil) :$$ a
project Type = TypeF
project (Pi t b) = PiF t b

embed :: CoreF () Core a -> Core a
embed (LamF p b) = Lam p b
embed (f :$$ a) = f $$* a
embed TypeF = Type
embed (PiF t b) = Pi t b


global :: Qualified -> Core (Name a)
global = (:$ Nil) . Global

lam :: Eq a => Plicit a -> Core a -> Core a
lam (pl :< n) b = Lam pl (bind1 n b)

lams :: (Eq a, Foldable t) => t (Plicit a) -> Core a -> Core a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Core a -> m (Plicit a, Core a)
unlam n (Lam p b) = pure (p :< n, instantiate1 (pure n) b)
unlam _ _         = empty

pi :: Eq a => Plicit (a ::: Used (Core a)) -> Core a -> Core a
pi (p :< n ::: t) b = Pi (p :< t) (bind1 n b)

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t) => t (Plicit (a ::: Used (Core a))) -> Core a -> Core a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Core a -> m (Plicit (a ::: Used (Core a)), Core a)
unpi n (Pi (p :< t) b) = pure (p :< n ::: t, instantiate1 (pure n) b)
unpi _ _               = empty

($$) :: Core a -> Plicit (Core a) -> Core a
Lam _ b $$ (_ :< v) = instantiate1 v b
Pi _  b $$ (_ :< v) = instantiate1 v b
n :$ vs $$ v        = n :$ (vs :> v)
_       $$ _        = error "illegal application of Type"

($$*) :: Foldable t => Core a -> t (Plicit (Core a)) -> Core a
v $$* sp = foldl' ($$) v sp


eiter :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . CoreF () n a -> n a)
      -> (forall a . Incr () (n a) -> m (Incr () (n a)))
      -> (a -> m b)
      -> Core a
      -> n b
eiter var alg k = go
  where go :: forall x y . (x -> m y) -> Core x -> n y
        go h = alg . \case
          Lam p b -> LamF p (foldScope k go h b)
          f :$ a -> var (h f) :$$ (fmap (go h) <$> a)
          Type -> TypeF
          Pi t b -> PiF (fmap (go h) <$> t) (foldScope k go h b)


generalizeType :: Core (Name Meta) -> Core Qualified
generalizeType ty = name undefined id <$> uncurry pis (traverse (traverse f) ty)
  where f v = let name = case v of { Name n -> n ; Meta n -> n } in (Set.singleton (Im :< Local name ::: Zero :@ Type), name)


weaken :: Functor f => f Qualified -> f (Name a)
weaken = fmap Global

strengthen :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => Core (Name Meta) -> m (Core Qualified)
strengthen ty = case traverse strengthenVar ty of
  Failure e -> unsolvedMetavariables (toList e) ty
  Success a -> pure a
  where strengthenVar (Global q) = Success q
        strengthenVar (Local v)  = Failure (Set.singleton v)

data Validation e a
  = Failure e
  | Success a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Semigroup e => Applicative (Validation e) where
  pure = Success
  Failure e1 <*> Failure e2 = Failure (e1 <> e2)
  Failure e1 <*> _          = Failure e1
  _          <*> Failure e2 = Failure e2
  Success f  <*> Success a  = Success (f a)


unsolvedMetavariables :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => [Meta] -> Core (Name Meta) -> m a
unsolvedMetavariables metas ty = do
  span <- ask
  throwError (prettyErr span (pretty "unsolved metavariable" <> (if length metas == 1 then mempty else pretty "s") <+> fillSep (punctuate comma (map pretty metas))) [pretty ty])


-- $setup
-- >>> import Test.QuickCheck
