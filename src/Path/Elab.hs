{-# LANGUAGE DeriveFunctor, KindSignatures #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Fail
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

type Result = Either String

infer :: (Carrier sig m, MonadFail m) => Int -> Context -> Term Surface -> m Elab
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
infer _ ctx (Term (Core (Free n))) = maybe (fail ("free variable: " <> show n)) (pure . elab (Free n)) (Map.lookup n ctx)
infer i ctx (Term (Core (f :@ a))) = do
  f' <- infer i ctx f
  case elabType f' of
    VPi t t' -> do
      a' <- check i ctx a t
      pure (elab (f' :@ a') (t' (eval (erase a') [])))
    _ -> fail ("illegal application of " <> show f')
infer _ _ tm = fail ("no rule to infer type of " <> show tm)

check :: (Carrier sig m, MonadFail m) => Int -> Context -> Term Surface -> Type -> m Elab
check i ctx (Term (Core (Lam e))) (VPi t t') = do
  e' <- check (succ i) (Map.insert (Local i) t ctx) (subst 0 (Term (Core (Free (Local i)))) e) (t' (vfree (Local i)))
  pure (elab (Lam e') (VPi t t'))
check i ctx tm ty = do
  v <- infer i ctx tm
  unless (elabType v == ty) (fail ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v
