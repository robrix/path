{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, MultiParamTypeClasses #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader hiding (Local)
import Control.Monad (unless)
import qualified Data.Map as Map
import Data.Text.Prettyprint.Doc
import Path.Core
import Path.Eval
import Path.FreeVariables
import Path.Name
import Path.Pretty
import Path.Recursive
import Path.Surface
import Path.Term
import Prelude hiding (fail)

type Type = Value


newtype Elab a = Elab (ElabF Core a (Elab a))
  deriving (Eq, Ord, PrettyPrec, Show)

instance FreeVariables a => FreeVariables (Elab a) where
  fvs = cata (liftFvs id)

unElab :: Elab a -> ElabF Core a (Elab a)
unElab (Elab elabF) = elabF

data ElabF f a b = ElabF (f b) a
  deriving (Eq, Functor, Ord, Show)

instance (PrettyPrec a, PrettyPrec (f b)) => PrettyPrec (ElabF f a b) where
  prettyPrec d (ElabF core ty) = prettyParens (d > 0) $ prettyPrec 1 core <> pretty " : " <> prettyPrec 1 ty

instance (FreeVariables a, FreeVariables1 f) => FreeVariables1 (ElabF f a) where
  liftFvs fvs' (ElabF tm ty) = liftFvs fvs' tm <> fvs ty

elabFExpr :: ElabF f a b -> f b
elabFExpr (ElabF expr _) = expr

elabFType :: ElabF f a b -> a
elabFType (ElabF _ ty) = ty

instance Recursive (ElabF Core a) (Elab a) where project = unElab

elab :: Core (Elab a) -> a -> Elab a
elab = fmap Elab . ElabF

elabType :: Elab a -> a
elabType = elabFType . unElab

erase :: Elab a -> Term Core
erase = cata (Term . elabFExpr)


type Context = Map.Map Name Value

infer :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Env) sig, MonadFail m) => Term Surface -> m (Elab Type)
infer (Term (Ann e t)) = do
  t' <- check t VType
  env <- ask
  let t'' = eval (erase t') env
  check e t''
infer (Term (Core Type)) = pure (elab Type VType)
infer (Term (Core (Pi n e t b))) = do
  t' <- check t VType
  env <- ask
  let t'' = eval (erase t') env
  b' <- local (Map.insert (Local n) t'') (check (subst n (Term (Core (Free (Local n)))) b) VType)
  pure (elab (Pi n e t' b') VType)
infer (Term (Core (Free n))) = asks (Map.lookup n) >>= maybe (fail ("free variable: " <> show n)) (pure . elab (Free n))
infer (Term (Core (f :@ a))) = do
  f' <- infer f
  case elabType f' of
    VPi _ _ t t' -> do
      a' <- check a t
      env <- ask
      pure (elab (f' :@ a') (t' (eval (erase a') env)))
    _ -> fail ("illegal application of " <> show f')
infer tm = fail ("no rule to infer type of " <> show tm)

check :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Env) sig, MonadFail m) => Term Surface -> Type -> m (Elab Type)
check (Term (Core (Lam n e))) (VPi tn ann t t') = do
  e' <- local (Map.insert (Local n) t) (check (subst n (Term (Core (Free (Local n)))) e) (t' (vfree (Local n))))
  pure (elab (Lam n e') (VPi tn ann t t'))
check tm ty = do
  v <- infer tm
  unless (elabType v == ty) (fail ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v
