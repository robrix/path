{-# LANGUAGE FlexibleContexts #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader hiding (Local)
import Control.Monad (unless)
import qualified Data.Map as Map
import Data.Text.Prettyprint.Doc
import Path.Core
import Path.Eval
import Path.Name
import Path.Surface
import Path.Term
import Prelude hiding (fail)

type Type = Value

type Context = Map.Map Name Value

elab :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Env) sig, MonadFail m) => Term Surface -> Maybe Type -> m (Term (Ann Core Type))
elab (In (e ::: t)) Nothing = do
  t' <- check t VType
  env <- ask
  let t'' = eval (erase t') env
  check e t''
elab (In (Core Type)) Nothing = pure (In (Ann Type VType))
elab (In (Core (Pi n e t b))) Nothing = do
  t' <- check t VType
  env <- ask
  let t'' = eval (erase t') env
  b' <- local (Map.insert (Local n) t'') (check (subst n (In (Core (Free (Local n)))) b) VType)
  pure (In (Ann (Pi n e t' b') VType))
elab (In (Core (Free n))) Nothing = asks (Map.lookup n) >>= maybe (fail ("free  variable: " <> show n)) (pure . In . Ann (Free n))
elab (In (Core (f :@ a))) Nothing = do
  f' <- infer f
  case ann (out f') of
    VPi _ _ t t' -> do
      a' <- check a t
      env <- ask
      pure (In (Ann (f' :@ a') (t' (eval (erase a') env))))
    _ -> fail ("illegal application of " <> show f')
elab tm Nothing = fail ("no rule to infer type of " <> show tm)
elab (In (Core (Lam n e))) (Just (VPi tn ann t t')) = do
  e' <- local (Map.insert (Local n) t) (check (subst n (In (Core (Free (Local n)))) e) (t' (vfree (Local n))))
  pure (In (Ann (Lam n e') (VPi tn ann t t')))
elab tm (Just ty) = do
  v <- infer tm
  unless (ann (out v) == ty) (fail ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v

infer :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Env) sig, MonadFail m) => Term Surface -> m (Term (Ann Core Type))
infer tm = elab tm Nothing

check :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Env) sig, MonadFail m) => Term Surface -> Type -> m (Term (Ann Core Type))
check tm = elab tm . Just


data Err
  = FreeVariable Name
  | TypeMismatch Type Type
  | NoRuleToInfer (Term Surface)
  | IllegalApplication (Term (Ann Core Type))
  deriving (Eq, Ord, Show)
