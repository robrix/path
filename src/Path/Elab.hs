{-# LANGUAGE DeriveFunctor, FlexibleContexts, KindSignatures #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Fail
import Control.Effect.Reader hiding (Local)
import Control.Monad (unless)
import Data.Coerce
import qualified Data.Map as Map
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


type Context = Map.Map Name Value

infer :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Int) sig, MonadFail m) => Term Surface -> m Elab
infer (Term (Ann e t)) = do
  t' <- check t VType
  let t'' = eval (erase t') []
  check e t''
infer (Term (Core Type)) = pure (elab Type VType)
infer (Term (Core (Pi t b))) = do
  t' <- check t VType
  let t'' = eval (erase t') []
  i <- ask
  b' <- local (Map.insert (Local i) t'') (local (const (succ i)) (check (subst 0 (Term (Core (Free (Local i)))) b) VType))
  pure (elab (Pi t' b') VType)
infer (Term (Core (Free n))) = (asks (Map.lookup n)) >>= maybe (fail ("free variable: " <> show n)) (pure . elab (Free n))
infer (Term (Core (f :@ a))) = do
  f' <- infer f
  case elabType f' of
    VPi t t' -> do
      a' <- check a t
      pure (elab (f' :@ a') (t' (eval (erase a') [])))
    _ -> fail ("illegal application of " <> show f')
infer tm = fail ("no rule to infer type of " <> show tm)

check :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Int) sig, MonadFail m) => Term Surface -> Type -> m Elab
check (Term (Core (Lam e))) (VPi t t') = do
  i <- ask
  e' <- local (Map.insert (Local i) t) (local (const (succ i)) (check (subst 0 (Term (Core (Free (Local i)))) e) (t' (vfree (Local i)))))
  pure (elab (Lam e') (VPi t t'))
check tm ty = do
  v <- infer tm
  unless (elabType v == ty) (fail ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v
