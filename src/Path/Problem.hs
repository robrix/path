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
import           Path.Pretty
import           Path.Scope
import           Path.Syntax
import           Path.Term
import           Prelude hiding (pi)

instance Pretty a => Pretty (Term (Problem :+: Core) a) where
  pretty = prettyTerm (\ go -> \case
    L p -> prettyProblem go p
    R c -> prettyCore    go c)

prettyProblem :: (Carrier sig m, Member (Reader N) sig, Member (Writer (Set.Set N)) sig, Monad f) => (f (m Prec) -> m Prec) -> Problem f (m Prec) -> m Prec
prettyProblem go = \case
  Ex t b -> do
    t' <- withPrec 1 <$> go t
    (n, b') <- binding go prettyMeta b
    pure (prec 0 (magenta (pretty "∃") <+> pretty (n ::: t') </> magenta dot <+> withPrec 0 b'))
  p1 :===: p2 -> do
    p1' <- withPrec 1 <$> go p1
    p2' <- withPrec 1 <$> go p2
    pure (prec 0 (flatAlt (p1' <+> eq' <+> p2') (align (space <+> p1' </> eq' <+> p2'))))
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
