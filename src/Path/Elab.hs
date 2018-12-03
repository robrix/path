{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, KindSignatures, MultiParamTypeClasses #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Fail
import Control.Effect.Reader hiding (Local)
import Control.Monad (unless)
import Data.Coerce
import Data.Function (fix)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Eval
import Path.Expr
import Prelude hiding (fail)

data Elaborate (m :: * -> *) k
  = Infer (Term Surface) (Elab -> k)
  | Check (Term Surface) Type (Elab -> k)
  | Define Elab k
  deriving (Functor)

instance HFunctor Elaborate where
  hmap _ = coerce

instance Effect Elaborate where
  handle state handler = coerce . fmap (handler . (<$ state))

type Type = Value

showType :: Int -> Type -> ShowS
showType d = showCoreTerm d . quote


newtype Elab = Elab (ElabF Core Elab)
  deriving (Eq, Ord)

instance Show Elab where
  showsPrec = fix (\ f d (Elab (ElabF core ty)) -> showParen (d > 0) $ showCore f (cata elabFVs) 1 core . showString " : " . showType 1 ty)

unElab :: Elab -> ElabF Core Elab
unElab (Elab elabF) = elabF

data ElabF f a = ElabF (f a) Type
  deriving (Eq, Functor, Ord, Show)

elabFExpr :: ElabF f a -> f a
elabFExpr (ElabF expr _) = expr

elabFType :: ElabF f a -> Type
elabFType (ElabF _ ty) = ty

elabFVs :: ElabF Core (Set.Set Name) -> Set.Set Name
elabFVs (ElabF tm ty) = coreFVs tm <> cata coreFVs (quote ty)

instance Recursive (ElabF Core) Elab where project = unElab

elab :: Core Elab -> Type -> Elab
elab = fmap Elab . ElabF

elabType :: Elab -> Type
elabType = elabFType . unElab

erase :: Elab -> Term Core
erase = cata (Term . elabFExpr)


type Context = Map.Map Name Value

infer :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Term Surface -> m Elab
infer (Term (Ann e t)) = do
  t' <- check t VType
  let t'' = eval (erase t') mempty
  check e t''
infer (Term (Core Type)) = pure (elab Type VType)
infer (Term (Core (Pi n t b))) = do
  t' <- check t VType
  let t'' = eval (erase t') mempty
  b' <- local (Map.insert (Local n) t'') (check (subst n (Term (Core (Free (Local n)))) b) VType)
  pure (elab (Pi n t' b') VType)
infer (Term (Core (Free n))) = asks (Map.lookup n) >>= maybe (fail ("free variable: " <> show n)) (pure . elab (Free n))
infer (Term (Core (f :@ a))) = do
  f' <- infer f
  case elabType f' of
    VPi _ t t' -> do
      a' <- check a t
      pure (elab (f' :@ a') (t' (eval (erase a') mempty)))
    _ -> fail ("illegal application of " <> show f')
infer tm = fail ("no rule to infer type of " <> show tm)

check :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Term Surface -> Type -> m Elab
check (Term (Core (Lam n e))) (VPi tn t t') = do
  e' <- local (Map.insert (Local n) t) (check (subst n (Term (Core (Free (Local n)))) e) (t' (vfree (Local n))))
  pure (elab (Lam n e') (VPi tn t t'))
check tm ty = do
  v <- infer tm
  unless (elabType v == ty) (fail ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v
