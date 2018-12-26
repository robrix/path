{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Control.Effect
import Control.Effect.Reader hiding (Reader(Local))
import Data.Foldable (foldl')
import Data.Maybe (fromMaybe)
import Path.Core as Core
import Path.Env as Env
import Path.Name
import Path.Term
import Path.Value as Value

eval :: (Applicative m, Carrier sig m, Member (Reader Env) sig) => Term Core a -> m Value
eval = \case
  In (Core.Var n) _
    | isLocal n -> fromMaybe (vfree n) <$> asks (Env.lookup n)
    | otherwise -> pure (vfree n)
  In (Core.Lam n b) _ -> Value.Lam n <$> local (Env.insert (Local n) (vfree (Local n))) (eval b)
  In (f :@ a) _ -> vapp <$> eval f <*> eval a
  In Core.Type _ -> pure (Value.Type)
  In (Core.Pi n e ty b) _ -> Value.Pi n e <$> eval ty <*> local (Env.insert (Local n) (vfree (Local n))) (eval b)

vforce :: (Carrier sig m, Member (Reader Env) sig, Monad m) => Value -> m Value
vforce = \case
  Value.Lam v b      -> Value.Lam v <$> vforce b
  Value.Type         -> pure Value.Type
  Value.Pi v u t b   -> Value.Pi v u <$> vforce t <*> vforce b
  Value.Neutral vs n -> foldl' app (asks (Env.lookup n) >>= maybe (pure (vfree n)) vforce) vs
  where app f a = vapp <$> f <*> vforce a
