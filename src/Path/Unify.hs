{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Reader(Local))
import Path.Context
import Path.Env as Env
import Path.Eval
import Path.Name
import Path.Value

unifiesWith :: (Carrier sig m, Member Fresh sig, Member (Reader Env) sig, Monad m) => Type QName -> Type QName -> m Bool
unifiesWith = curry $ \case
  (Type, Type) -> pure True
  (Lam n1 b1, Lam n2 b2) -> do
    n <- freshName
    local (Env.insert (Local n1) (vfree n) . Env.insert (Local n2) (vfree n)) (b1 `unifiesWith` b2)
  (t1, t2) -> do
    t1' <- vforce t1
    pure (t1' `aeq` t2)


freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m QName
freshName = Local . Gensym <$> fresh
