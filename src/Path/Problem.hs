{-# LANGUAGE DataKinds, DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Problem where

import Control.Applicative (Alternative (..))
import Control.Effect.Carrier
import GHC.Generics (Generic1)
import Path.Core
import Path.Fin
import Path.Nat
import Path.Pretty
import Path.Scope
import Path.Syntax
import Path.Vec
import Prelude hiding (pi)
import Syntax.Module
import Syntax.Scope
import Syntax.Sum
import Syntax.Term
import Syntax.Var

-- FIXME: represent errors explicitly in the tree
-- FIXME: represent spans explicitly in the tree
data Problem f a
  = Ex (f a) (Scope () f a)
  | Unify (Equation (f a))
  deriving (Foldable, Functor, Generic1, HFunctor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Problem f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Problem f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (Problem f a)

instance RightModule Problem where
  Ex t b  >>=* f = Ex (t >>= f) (b >>=* f)
  Unify q >>=* f = Unify ((>>= f) <$> q)


exists :: (Eq a, Carrier sig m, Member Problem sig) => a ::: m a -> m a -> m a
exists (n ::: t) b = send (Ex t (abstract1 n b))

existsFin :: (Carrier sig m, Member Problem sig) => m (Var (Fin n) a) -> m (Var (Fin ('S n)) a) -> m (Var (Fin n) a)
existsFin t b = send (Ex t (toScopeFin b))

unexists :: (Alternative m, Project Problem sig, RightModule sig) => a -> Term sig a -> m (a ::: Term sig a, Term sig a)
unexists n t | Just (Ex t b) <- prjTerm t = pure (n ::: t, instantiate1 (pure n) b)
unexists _ _                              = empty

unexistsFin :: (Alternative m, Project Problem sig, RightModule sig) => Term sig (Var (Fin n) a) -> m (Term sig (Var (Fin n) a), Term sig (Var (Fin ('S n)) a))
unexistsFin t | Just (Ex t b) <- prjTerm t = pure (t, fromScopeFin b)
unexistsFin _                              = empty


(===) :: (Carrier sig m, Member Problem sig) => m a -> m a -> m a
p === q = send (Unify (p :===: q))

infixr 3 ===


instance Pretty a => Pretty (Term (Problem :+: Core) a) where
  pretty = prettyTerm (\ go ctx -> \case
    L p -> prettyProblem go ctx p
    R c -> prettyCore    go ctx c)

prettyProblem
  :: Monad f
  => (forall n . Vec n Doc -> f (Var (Fin n) a) -> Prec Doc)
  -> Vec n Doc
  -> Problem f (Var (Fin n) a)
  -> Prec Doc
prettyProblem go ctx = \case
  Ex t b ->
    let t' = withPrec 1 (go ctx t)
        n  = prettyMeta @Doc (prettyVar (length ctx))
        b' = withPrec 0 (go (n :# ctx) (fromScopeFin b))
    in prec 0 (group (vsep [magenta (pretty "∃") <+> pretty (n ::: t'), magenta dot <+> b']))
  Unify (p1 :===: p2) ->
    let p1' = withPrec 1 (go ctx p1)
        p2' = withPrec 1 (go ctx p2)
    in prec 0 (flatAlt (p1' <+> eq' <+> p2') (align (group (vsep [space <+> p1', eq' <+> p2']))))
  where eq' = magenta (pretty "≡")
