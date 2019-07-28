{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Problem where

import           Control.Applicative (Alternative (..))
import           Control.Effect.Carrier
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.Writer
import           Control.Monad.Module
import qualified Data.Set as Set
import           GHC.Generics (Generic1)
import           Path.Core
import           Path.Name
import           Path.Pretty hiding (prec, withPrec)
import           Path.Scope
import           Path.Syntax
import           Path.Term
import           Prelude hiding (pi)

newtype P = P { unP :: Int }
  deriving (Eq, Ord, Show)

instance Pretty (Term (Problem :+: Core) Qualified) where
  pretty = snd . run . runWriter @(Set.Set N) . runReader (P 0) . runReader (N 0) . go . fmap (pure . pretty)
    where go = \case
            Var v -> v
            Term (R c) -> prettyCore go c
            Term (L p) -> prettyProblem go p

prec :: (Carrier sig m, Member (Reader P) sig) => Int -> Doc -> m Doc
prec d' doc = do
  d <- ask
  pure (prettyParens (d > P d') doc)

withPrec :: (Carrier sig m, Member (Reader P) sig) => Int -> m a -> m a
withPrec i = local (const (P i))

prettyMeta :: Pretty a => a -> Doc
prettyMeta n = dullblack (bold (pretty '?' <> pretty n))

binding :: (Carrier sig m, Member (Reader N) sig, Member (Writer (Set.Set N)) sig, Monad f) => (f (m Doc) -> m Doc) -> (N -> Doc) -> Scope a f (m Doc) -> m (N, Doc)
binding go pretty m = do
  n <- ask @N
  (,) n <$> local @N succ (go (instantiate1 (pure (tell (Set.singleton n) *> pure (pretty n))) m))

prettyCore :: (Carrier sig m, Member (Reader N) sig, Member (Reader P) sig, Member (Writer (Set.Set N)) sig, Monad f) => (f (m Doc) -> m Doc) -> Core f (m Doc) -> m Doc
prettyCore go = \case
  Lam b -> do
    (n, b') <- withPrec 0 (binding go pretty b)
    prec 0 (pretty (cyan backslash) <+> pretty n </> cyan dot <+> b')
  f :$ a -> do
    f' <- withPrec 10 (go f)
    a' <- withPrec 11 (go a)
    prec 10 (f' <+> a')
  Let v b -> do
    v' <- withPrec 0 (go v)
    (n, b') <- withPrec 0 (binding go prettyMeta b)
    prec 0 (magenta (pretty "let") <+> pretty (n := v') </> magenta dot <+> b')
  Type -> pure (yellow (pretty "Type"))
  Pi t b -> do
    t' <- withPrec 1 (go t)
    (fvs, (n, b')) <- listen (withPrec 0 (binding go pretty b))
    let t'' | n `Set.member` fvs = parens (pretty (n ::: t'))
            | otherwise          = t'
    prec 0 (t'' </> arrow <+> b')
  where arrow = blue (pretty "→")

prettyProblem :: (Carrier sig m, Member (Reader N) sig, Member (Reader P) sig, Member (Writer (Set.Set N)) sig, Monad f) => (f (m Doc) -> m Doc) -> Problem f (m Doc) -> m Doc
prettyProblem go = \case
  Ex t b -> do
    t' <- withPrec 1 (go t)
    (n, b') <- withPrec 0 (binding go prettyMeta b)
    prec 0 (magenta (pretty "∃") <+> pretty (n ::: t') </> magenta dot <+> b')
  p1 :===: p2 -> do
    p1' <- withPrec 1 (go p1)
    p2' <- withPrec 1 (go p2)
    prec 0 (flatAlt (p1' <+> eq' <+> p2') (align (space <+> p1' </> eq' <+> p2')))
  where eq' = magenta (pretty "≡")


-- FIXME: represent errors explicitly in the tree
-- FIXME: represent spans explicitly in the tree
data Problem f a
  = Ex (f a) (Scope () f a)
  | f a :===: f a
  deriving (Foldable, Functor, Generic1, HFunctor, Traversable)

infix 3 :===:

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Problem f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Problem f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (Problem f a)

instance RightModule Problem where
  Ex t b    >>=* f = Ex (t >>= f) (b >>=* f)
  p :===: q >>=* f = (p >>= f) :===: (q >>= f)


exists :: (Eq a, Carrier sig m, Member Problem sig) => a ::: m a -> m a -> m a
exists (n ::: t) b = send (Ex t (bind1 n b))

unexists :: (Alternative m, Member Problem sig, RightModule sig) => a -> Term sig a -> m (a ::: Term sig a, Term sig a)
unexists n (Term t) | Just (Ex t b) <- prj t = pure (n ::: t, instantiate1 (pure n) b)
unexists _ _                                 = empty

(===) :: (Carrier sig m, Member Problem sig) => m a -> m a -> m a
p === q = send (p :===: q)

infixr 3 ===
