{-# LANGUAGE FlexibleContexts #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Reader(Local))
import Control.Monad (unless, void)
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
            Lam n <$> local (bind n1 n2 n)
              (local (Context.insert (Local tn) t) (check b b1 b2))
          (Type, Pi n1 u1 t1 b1, Pi n2 u2 t2 b2) -> do
            n <- freshName
            Pi n (u1 `max` u2)
              <$> check Type t1 t2
              <*> local (bind n1 n2 n)
                (check Type b1 b2)
          (ty1, Neutral{}, Neutral{}) -> do
            (tm, ty2) <- infer t1 t2
            void $ check Type ty1 ty2
            pure tm
          (_, t1, t2) -> do
            t1' <- vforce t1
            unless (t1' `aeq` t2) (throwError (TypeMismatch t1 t2 span))
            pure t1'

        infer _ _ = ask >>= \ ctx -> throwError (NoRuleToInfer (Context.filter (const . isLocal) ctx) span)

bind :: Name -> Name -> Name -> Env -> Env
bind n1 n2 n = Env.insert (Local n1) n' . Env.insert (Local n2) n'
  where n' = vfree (Local n)

freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m Name
freshName = Gensym <$> fresh
