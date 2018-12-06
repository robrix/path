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
import Path.Name
import Path.Surface
import Path.Term
import Prelude hiding (fail)

type Type = Value

type Context = Map.Map Name Value

infer :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Env) sig, MonadFail m) => Term Surface -> m (Ann Core Type)
infer (Term (e ::: t)) = do
  t' <- check t VType
  env <- ask
  let t'' = eval (erase t') env
  check e t''
infer (Term (Core Type)) = pure (Ann Type VType)
infer (Term (Core (Pi n e t b))) = do
  t' <- check t VType
  env <- ask
  let t'' = eval (erase t') env
  b' <- local (Map.insert (Local n) t'') (check (subst n (Term (Core (Free (Local n)))) b) VType)
  pure (Ann (Pi n e t' b') VType)
infer (Term (Core (Free n))) = asks (Map.lookup n) >>= maybe (fail ("free variable: " <> show n)) (pure . Ann (Free n))
infer (Term (Core (f :@ a))) = do
  f' <- infer f
  case ann f' of
    VPi _ _ t t' -> do
      a' <- check a t
      env <- ask
      pure (Ann (f' :@ a') (t' (eval (erase a') env)))
    _ -> fail ("illegal application of " <> show f')
infer tm = fail ("no rule to infer type of " <> show tm)

check :: (Carrier sig m, Member (Reader Context) sig, Member (Reader Env) sig, MonadFail m) => Term Surface -> Type -> m (Ann Core Type)
check (Term (Core (Lam n e))) (VPi tn ann t t') = do
  e' <- local (Map.insert (Local n) t) (check (subst n (Term (Core (Free (Local n)))) e) (t' (vfree (Local n))))
  pure (Ann (Lam n e') (VPi tn ann t t'))
check tm ty = do
  v <- infer tm
  unless (ann v == ty) (fail ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v
