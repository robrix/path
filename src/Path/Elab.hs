{-# LANGUAGE DeriveFunctor, KindSignatures #-}
module Path.Elab where

import Control.Effect.Carrier
import Control.Monad (unless)
import Data.Coerce
import qualified Data.Map as Map
import Path.Expr

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

type Result = Either String

infer :: Int -> Context -> Term Surface -> Result Elab
infer i ctx (Term (Ann e t)) = do
  t' <- check i ctx t VType
  let t'' = eval (erase t') []
  check i ctx e t''
infer _ _ (Term (Core Type)) = pure (elab Type VType)
infer i ctx (Term (Core (Pi t b))) = do
  t' <- check i ctx t VType
  let t'' = eval (erase t') []
  b' <- check (succ i) (Map.insert (Local i) t'' ctx) (subst 0 (Term (Core (Free (Local i)))) b) VType
  pure (elab (Pi t' b') VType)
infer _ ctx (Term (Core (Free n))) = maybe (Left ("free variable: " <> show n)) (pure . elab (Free n)) (Map.lookup n ctx)
infer i ctx (Term (Core (f :@ a))) = do
  f' <- infer i ctx f
  case elabType f' of
    VPi t t' -> do
      a' <- check i ctx a t
      pure (elab (f' :@ a') (t' (eval (erase a') [])))
    _ -> Left ("illegal application of " <> show f')
infer _ _ tm = Left ("no rule to infer type of " <> show tm)

check :: Int -> Context -> Term Surface -> Type -> Result Elab
check i ctx (Term (Core (Lam e))) (VPi t t') = do
  e' <- check (succ i) (Map.insert (Local i) t ctx) (subst 0 (Term (Core (Free (Local i)))) e) (t' (vfree (Local i)))
  pure (elab (Lam e') (VPi t t'))
check i ctx tm ty = do
  v <- infer i ctx tm
  unless (elabType v == ty) (Left ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v
