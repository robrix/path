{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
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


newtype Ann f a = Ann (AnnF f a (Ann f a))
  deriving (FreeVariables)

deriving instance (Eq a, Eq (f (Ann f a))) => Eq (Ann f a)
deriving instance (Ord a, Ord (f (Ann f a))) => Ord (Ann f a)
deriving instance (Show a, Show (f (Ann f a))) => Show (Ann f a)
deriving instance (PrettyPrec a, PrettyPrec (f (Ann f a))) => PrettyPrec (Ann f a)

unElab :: Ann f a -> AnnF f a (Ann f a)
unElab (Ann elabF) = elabF

data AnnF f a b = AnnF (f b) a
  deriving (Eq, Functor, Ord, Show)

instance (PrettyPrec a, PrettyPrec (f b)) => PrettyPrec (AnnF f a b) where
  prettyPrec d (AnnF core ty) = prettyParens (d > 0) $ prettyPrec 1 core <> pretty " : " <> prettyPrec 1 ty

instance (FreeVariables a, FreeVariables1 f) => FreeVariables1 (AnnF f a) where
  liftFvs fvs' (AnnF tm ty) = liftFvs fvs' tm <> fvs ty

instance (FreeVariables a, FreeVariables b, FreeVariables1 f) => FreeVariables (AnnF f a b) where
  fvs = fvs1

elabFExpr :: AnnF f a b -> f b
elabFExpr (AnnF expr _) = expr

elabFType :: AnnF f a b -> a
elabFType (AnnF _ ty) = ty

instance Functor f => Recursive (AnnF f a) (Ann f a) where project = unElab

elab :: f (Ann f a) -> a -> Ann f a
elab = fmap Ann . AnnF

elabType :: Ann f a -> a
elabType = elabFType . unElab

erase :: Functor f => Ann f a -> Term f
erase = cata (Term . elabFExpr)


type Context = Map.Map Name Value

infer :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Env) sig, MonadFail m) => Term Surface -> m (Ann Core Type)
infer (Term (e ::: t)) = do
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

check :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Env) sig, MonadFail m) => Term Surface -> Type -> m (Ann Core Type)
check (Term (Core (Lam n e))) (VPi tn ann t t') = do
  e' <- local (Map.insert (Local n) t) (check (subst n (Term (Core (Free (Local n)))) e) (t' (vfree (Local n))))
  pure (elab (Lam n e') (VPi tn ann t t'))
check tm ty = do
  v <- infer tm
  unless (elabType v == ty) (fail ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v
