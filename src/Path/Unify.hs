{-# LANGUAGE FlexibleContexts #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Reader(Local))
import Control.Monad (unless)
import Path.Context
import Path.Env as Env
import Path.Error
import Path.Eval
import Path.Name
import Path.Value
import Text.Trifecta.Rendering (Span)

unifyWith :: (Carrier sig m, Member (Error ElabError) sig, Member Fresh sig, Member (Reader Env) sig, Monad m) => Span -> Type QName -> Type QName -> m ()
unifyWith span t1 t2 = case (t1, t2) of
  (Type, Type) -> pure ()
  (Lam n1 b1, Lam n2 b2) -> do
    n <- freshName
    local (Env.insert (Local n1) (vfree n) . Env.insert (Local n2) (vfree n)) (unifyWith span b1 b2)
  (t1, t2) -> do
    t1' <- vforce t1
    unless (t1' `aeq` t2) (throwError (TypeMismatch t1 t2 span))


freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m QName
freshName = Local . Gensym <$> fresh
