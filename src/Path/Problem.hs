{-# LANGUAGE DataKinds, DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Problem where

import Control.Applicative (Alternative (..))
import Control.Carrier.Class
import Control.Monad.Module
import GHC.Generics (Generic1)
import Path.Core
import Path.Pretty
import Path.Scope
import Path.Syntax
import Path.Term
import Prelude hiding (pi)

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

existsFin :: (Carrier sig m, Member Problem sig) => m (Var (Fin n) a) -> m (Var (Fin ('S n)) a) -> m (Var (Fin n) a)
existsFin t b = send (Ex t (toScopeFin b))

unexists :: (Alternative m, Member Problem sig, RightModule sig) => a -> Term sig a -> m (a ::: Term sig a, Term sig a)
unexists n (Term t) | Just (Ex t b) <- prj t = pure (n ::: t, instantiate1 (pure n) b)
unexists _ _                                 = empty

(===) :: (Carrier sig m, Member Problem sig) => m a -> m a -> m a
p === q = send (p :===: q)

infixr 3 ===


instance Pretty a => Pretty (Term (Problem :+: Core) a) where
  pretty = prettyTerm (\ go ctx -> \case
    L p -> prettyProblem go ctx p
    R c -> prettyCore    go ctx c)

prettyProblem
  :: Monad f
  => (forall n . Vec n Doc -> f (Var (Fin n) a) -> Prec)
  -> Vec n Doc
  -> Problem f (Var (Fin n) a)
  -> Prec
prettyProblem go ctx = \case
  Ex t b ->
    let t' = withPrec 1 (go ctx t)
        n  = prettyMeta (prettyVar (length ctx))
        b' = withPrec 0 (go (VS n ctx) (fromScopeFin b))
    in prec 0 (group (vsep [magenta (pretty "∃") <+> pretty (n ::: t'), magenta dot <+> b']))
  p1 :===: p2 ->
    let p1' = withPrec 1 (go ctx p1)
        p2' = withPrec 1 (go ctx p2)
    in prec 0 (flatAlt (p1' <+> eq' <+> p2') (align (group (vsep [space <+> p1', eq' <+> p2']))))
  where eq' = magenta (pretty "≡")
