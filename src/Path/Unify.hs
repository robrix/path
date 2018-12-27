{-# LANGUAGE FlexibleContexts, TupleSections #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Reader(Local))
import Control.Monad (unless, void)
import Path.Back
import Path.Context as Context
import Path.Env as Env
import Path.Error
import Path.Eval
import Path.Name
import Path.Value
import Text.Trifecta.Rendering (Span)

unify :: (Carrier sig m, Member (Error ElabError) sig, Member Fresh sig, Member (Reader Context) sig, Member (Reader Env) sig, Monad m) => Span -> Type QName -> Type QName -> Type QName -> m (Type QName)
unify span = check
  where check ty t1 t2 = case (ty, t1, t2) of
          (Type, Type, Type) -> pure Type
          (Pi tn _ t b, Lam n1 b1, Lam n2 b2) -> do
            n <- freshName
            Lam n <$> local (Context.insert (Local tn) t) (check b b1 b2)
          (Type, Pi n1 u1 t1 b1, Pi n2 u2 t2 b2) -> do
            n <- freshName
            t <- check Type t1 t2
            Pi n (u1 `max` u2) t
              <$> local (Context.insert (Local n) t) (check Type b1 b2)
          (ty1, Neutral e1 h1, Neutral e2 h2) -> do
            (e, h, ty2) <- infer e1 h1 e2 h2
            void $ check Type ty1 ty2
            pure (Neutral e h)
          (_, t1, t2) -> do
            t1' <- vforce t1
            unless (t1' `aeq` t2) (throwError (TypeMismatch t1 t2 span))
            pure t1'

        infer e1 h1 e2 h2 = case (e1, h1, e2, h2) of
          (Nil, n1, Nil, n2)
            | n1 == n2 -> asks (Context.lookup n1) >>= maybe (throwError (FreeVariable n1 span)) (pure . (Nil, n1, ))
          (as1 :> a1, n1, as2 :> a2, n2) -> do
              (as, n, ty) <- infer as1 n1 as2 n2
              case ty of
                Pi tn _ t t' -> do
                  a <- check t a1 a2
                  pure (as :> a, n, subst (Local tn) a t') -- FIXME: unify the resource reqs
                _ -> throwError (IllegalApplication ty span)
          _ -> ask >>= \ ctx -> throwError (NoRuleToInfer (Context.filter (const . isLocal) ctx) span)

freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m Name
freshName = Gensym <$> fresh
