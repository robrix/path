{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
import Path.Back
import Path.Context as Context
import Path.Elab
import Path.Name
import Path.Value as Value

equal :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Monad m) => Type -> Type -> Type -> m Type
equal = check
  where check ty t1 t2 = case (ty, t1, t2) of
          (Type, Type, Type) -> pure Type
          (Type, Pi n1 u1 t1 b1, Pi n2 u2 t2 b2) | n1 == n2, u1 == u2 -> do
            t <- check Type t1 t2
            Pi n1 u1 t <$> local (Context.insert (Local n1) t) (check Type b1 b2)
          (Pi n _ t b, s1, s2) -> do
            b <- local (Context.insert (Local n) t) (check b (s1 `vapp` vfree (Local n)) (s2 `vapp` vfree (Local n)))
            pure (Lam n b)
          _ -> do
            (t, ty') <- infer t1 t2
            _ <- check Type ty ty'
            pure t

        infer t1 t2 = case (t1, t2) of
          (Neutral Nil n1, Neutral Nil n2) | n1 == n2 -> do
            ty <- asks (Context.lookup n1)
            maybe (throwError (FreeVariable n1 (error "what span???"))) (pure . (,) (Neutral Nil n1)) ty
          _ -> throwError (TypeMismatch t1 t2 (error "what span??"))

-- FIXME: metavariables at the head of neutral terms, but not bound by lambdas/etc
