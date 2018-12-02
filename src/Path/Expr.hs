{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Expr where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader hiding (Local)
import Control.Monad (unless)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Prelude hiding (fail)

data Name
  = Global String
  | Local Int
  deriving (Eq, Ord, Show)

prime :: Name -> Name
prime (Global n) = Global (n <> "ʹ")
prime (Local i) = Local (succ i)

fresh :: Set.Set Name -> Name
fresh = maybe (Local 0) (prime . fst) . Set.maxView


data Core a
  = Bound Int
  | Free Name
  | Abs Int a
  | App a a
  | Type
  | Pi Int a a
  deriving (Eq, Functor, Ord, Show)

data Surface a
  = Core (Core a)
  | Ann a (Type Surface)
  deriving (Eq, Functor, Ord, Show)

newtype Term f = Term { unTerm :: f (Term f) }

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)
deriving instance Show (f (Term f)) => Show (Term f)

instance Functor f => Recursive f (Term f) where
  project = unTerm

type Type = Term

freeVariables :: Type Core -> Set.Set Name
freeVariables = cata $ \ ty -> case ty of
  Bound n -> Set.singleton (Local n)
  Free n -> Set.singleton n
  Abs n b -> Set.delete (Local n) b
  App f a -> f <> a
  Type -> mempty
  Pi n t b -> t <> Set.delete (Local n) b

aeq :: Type Core -> Type Core -> Bool
aeq t1 t2 = run (runReader ([] :: [(Name, Name)]) (aeq' t1 t2))

aeq' :: (Carrier sig m, Member (Reader [(Name, Name)]) sig, Monad m) => Type Core -> Type Core -> m Bool
aeq' (Term Type) (Term Type) = pure True
aeq' (Term (Pi n1 t1 b1)) (Term (Pi n2 t2 b2)) = do
  t <- t1 `aeq'` t2
  if t then
    if n1 == n2 then
      b1 `aeq'` b2
    else do
      let n = fresh (freeVariables b1 <> freeVariables b2)
      local ((Local n1, n) :) (local ((Local n2, n) :) (b1 `aeq'` b2))
  else
    pure False
aeq' (Term (Bound n1)) (Term (Bound n2)) = do
  env <- ask
  pure (fromMaybe (Local n1) (lookup (Local n1) env) == fromMaybe (Local n2) (lookup (Local n2) env))
aeq' (Term (Free n1)) (Term (Free n2)) = do
  env <- ask
  pure (fromMaybe n1 (lookup n1 env) == fromMaybe n2 (lookup n2 env))
aeq' (Term (Abs n1 b1)) (Term (Abs n2 b2)) = do
  if n1 == n2 then
    b1 `aeq'` b2
  else do
    let n = fresh (freeVariables b1 <> freeVariables b2)
    local ((Local n1, n) :) (local ((Local n2, n) :) (b1 `aeq'` b2))
aeq' (Term (App f1 a1)) (Term (App f2 a2)) = do
  f <- f1 `aeq'` f2
  if f then
    a1 `aeq'` a2
  else
    pure False
aeq' _ _ = pure False

newtype Elab = Elab { unElab :: ElabF Core Elab }
  deriving (Eq, Ord, Show)

data ElabF f a = ElabF { elabFExpr :: f a, elabFType :: Value }
  deriving (Eq, Functor, Ord, Show)

instance Recursive (ElabF Core) Elab where project = unElab

erase :: Elab -> Term Core
erase = cata (Term . elabFExpr)

data Value
  = Closure Int (Term Core) Env
  | TypeV
  | PiV Int Value Value
  | Neutral Neutral
  deriving (Eq, Ord, Show)

data Neutral
  = FreeN Name
  | AppN Neutral Value
  deriving (Eq, Ord, Show)

quote :: Value -> Term Core
quote TypeV = Term Type
quote (Closure n b _) = Term (Abs n b)
quote (PiV n t b) = Term (Pi n (quote t) (quote b))
quote (Neutral n) = quoteN n

quoteN :: Neutral -> Term Core
quoteN (FreeN n) = Term (Free n)
quoteN (AppN n a) = Term (App (quoteN n) (quote a))


type Env = [(Name, Value)]

eval :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Term Core -> m Value
eval (Term (Bound name)) = do
  val <- asks (lookup (Local name))
  maybe (fail ("free variable: " <> show name)) pure val
eval (Term (Free name)) = pure (Neutral (FreeN name))
eval (Term (Abs name body)) = Closure name body <$> ask
eval (Term (App f a)) = do
  f' <- eval f
  case f' of
    Closure n b e -> do
      a' <- eval a
      local (const ((Local n, a') : e)) (eval b)
    Neutral n -> do
      a' <- eval a
      pure (Neutral (AppN n a'))
    v -> fail ("cannot apply " <> show v)
eval (Term Type) = pure TypeV
eval (Term (Pi name ty body)) = PiV name <$> eval ty <*> eval body

evalV :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Value -> m Value
evalV (Neutral n) = evalN n
evalV v = pure v

evalN :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Neutral -> m Value
evalN (FreeN n) = asks (lookup n) >>= maybe (pure (Neutral (FreeN n))) pure
evalN (AppN n a) = do
  n' <- evalN n
  case n' of
    Closure n b e -> do
      a' <- evalV a
      local (const ((Local n, a') : e)) (eval b)
    Neutral n'' -> Neutral . AppN n'' <$> evalV a
    v -> fail ("cannot apply " <> show v)

equate :: MonadFail m => Value -> Value -> m ()
equate ty1 ty2 =
  unless (quote ty1 `aeq` quote ty2) $
    fail ("could not judge " <> show ty1 <> " = " <> show ty2)

infer :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Term Surface -> m Elab
infer (Term (Core (Bound name))) = asks (lookup (Local name)) >>= maybe (fail ("free variable: " <> show name)) (pure . Elab . ElabF (Bound name))
infer (Term (Ann tm ty)) = do
  ty' <- erase <$> check ty TypeV
  ty'' <- eval ty'
  check tm ty''
infer (Term (Core (App f a))) = do
  f' <- infer f
  case f' of
    Elab (ElabF _ (PiV n t b)) -> do
      a' <- check a t
      a'' <- eval (erase a')
      b' <- local ((Local n, a'') :) (evalV b)
      pure (Elab (ElabF (App f' a') b'))
    _ -> fail ("illegal application of " <> show f <> " to " <> show a)
infer (Term (Core Type)) = pure (Elab (ElabF Type TypeV))
infer (Term (Core (Pi n t b))) = do
  t' <- check t TypeV
  t'' <- eval (erase t')
  b' <- local ((Local n, t'') :) (check b TypeV)
  pure (Elab (ElabF (Pi n t' b') TypeV))
infer term = fail ("no rule to infer type of term: " <> show term)

check :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Term Surface -> Value -> m Elab
check (Term (Core (Abs n b))) (PiV tn tt tb) = do
  b' <- local ((Local n, tt) :) (local ((Local tn, Neutral (FreeN (Local tn))) :) (check b tb))
  pure (Elab (ElabF (Abs n b') (PiV tn tt tb)))
check tm ty = do
  Elab (ElabF tm' elabTy) <- infer tm
  equate ty elabTy
  pure (Elab (ElabF tm' ty))


identity :: Term Surface
identity = Term (Core (Abs 0 (Term (Core (Bound 0)))))

constant :: Term Surface
constant = Term (Core (Abs 0 (Term (Core (Abs 1 (Term (Core (Bound 0))))))))


class Functor f => Recursive f t | t -> f where
  project :: t -> f t

cata :: Recursive f t => (f a -> a) -> t -> a
cata algebra = go
  where go = algebra . fmap go . project
