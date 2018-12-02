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

infer :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Int -> Term Surface -> m Elab
infer i (Term (Ann e t)) = do
  t' <- check i t VType
  let t'' = eval (erase t') []
  check i e t''
infer _ (Term (Core Type)) = pure (elab Type VType)
infer i (Term (Core (Pi t b))) = do
  t' <- check i t VType
  let t'' = eval (erase t') []
  b' <- local (Map.insert (Local i) t'') (check (succ i) (subst 0 (Term (Core (Free (Local i)))) b) VType)
  pure (elab (Pi t' b') VType)
infer _ (Term (Core (Free n))) = (asks (Map.lookup n)) >>= maybe (fail ("free variable: " <> show n)) (pure . elab (Free n))
infer i (Term (Core (f :@ a))) = do
  f' <- infer i f
  case elabType f' of
    VPi t t' -> do
      a' <- check i a t
      pure (elab (f' :@ a') (t' (eval (erase a') [])))
    _ -> fail ("illegal application of " <> show f')
infer _ tm = fail ("no rule to infer type of " <> show tm)

check :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Int -> Term Surface -> Type -> m Elab
check i (Term (Core (Lam e))) (VPi t t') = do
  e' <- local (Map.insert (Local i) t) (check (succ i) (subst 0 (Term (Core (Free (Local i)))) e) (t' (vfree (Local i))))
  pure (elab (Lam e') (VPi t t'))
check i tm ty = do
  v <- infer i tm
  unless (elabType v == ty) (fail ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v
