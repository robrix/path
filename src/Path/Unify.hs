{-# LANGUAGE FlexibleContexts #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Fresh
import Path.Context
import Path.Env
import Path.Eval
import Path.Name
import Path.Value

unifiesWith :: (Carrier sig m, Member (Reader Env) sig, Monad m) => Type QName -> Type QName -> m Bool
unifiesWith t1 t2 = vforce t1 >>= \ t1 -> pure (t1 `aeq` t2)

freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m QName
freshName = Local . Gensym <$> fresh
