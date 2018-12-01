{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Expr where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader
import Control.Monad (unless)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Prelude hiding (fail)

type Name = String

prime :: Name -> Name
prime n = n <> "ʹ"

fresh :: Set.Set Name -> Name
fresh = maybe "x" (prime . fst) . Set.maxView


data Core a
  = Var Name
  | Abs Name a
  | App a a
  | Type
  | Pi Name a a
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
  Var n -> Set.singleton n
  Abs n b -> Set.delete n b
  App f a -> f <> a
  Type -> mempty
  Pi n t b -> t <> Set.delete n b

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
      local (((n1, n) :) . ((n2, n) :)) (b1 `aeq'` b2)
  else
    pure False
aeq' (Term (Var n1)) (Term (Var n2)) = do
  env <- ask
  pure (fromMaybe n1 (lookup n1 env) == fromMaybe n2 (lookup n2 env))
aeq' (Term (Abs n1 b1)) (Term (Abs n2 b2)) = do
  if n1 == n2 then
    b1 `aeq'` b2
  else do
    let n = fresh (freeVariables b1 <> freeVariables b2)
    local (((n1, n) :) . ((n2, n) :)) (b1 `aeq'` b2)
aeq' (Term (App f1 a1)) (Term (App f2 a2)) = do
  f <- f1 `aeq'` f2
  if f then
    a1 `aeq'` a2
  else
    pure False
aeq' _ _ = pure False

newtype Elab = Elab { unElab :: ElabF Core Elab }
  deriving (Eq, Ord, Show)

data ElabF f a = ElabF { elabFExpr :: f a, elabFType :: Type Core }
  deriving (Eq, Functor, Ord, Show)

instance Recursive (ElabF Core) Elab where project = unElab

erase :: Elab -> Term Core
erase = cata (Term . elabFExpr)

data Value
  = Closure Name (Term Core) Env
  | TypeV
  deriving (Eq, Ord, Show)

quote :: Value -> Term Core
quote TypeV = Term Type
quote (Closure n b _) = Term (Abs n b)

type Env = [(Name, Value)]

eval :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Term Core -> m Value
eval (Term (Var name)) = do
  val <- asks (lookup name)
  maybe (fail ("free variable: " <> name)) pure val
eval (Term (Abs name body)) = Closure name body <$> ask
eval (Term (App f a)) = do
  f' <- eval f
  case f' of
    Closure n b e -> do
      a' <- eval a
      local (const ((n, a') : e)) (eval b)
    v -> fail ("cannot apply " <> show v)
eval (Term Type) = pure TypeV
eval (Term (Pi name _ body)) = Closure name body <$> ask


type Context = [(Name, Type Core)]

equate :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Type Core -> Type Core -> m ()
equate ty1 ty2 | ty1 `aeq` ty2 = pure ()
               | otherwise     = do
  ty1' <- eval ty1
  ty2' <- eval ty2
  unless (quote ty1' `aeq` quote ty2') $
    fail ("could not judge " <> show ty1 <> " = " <> show ty2)

infer :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Term Surface -> m Elab
infer (Term (Core (Var name))) = do
  ty <- asks (lookup name) >>= maybe (fail ("free variable: " <> name)) (pure . quote)
  pure (Elab (ElabF (Var name) ty))
infer (Term (Ann tm ty)) = check tm ty
infer (Term (Core Type)) = pure (Elab (ElabF Type (Term Type)))
infer term = fail ("no rule to infer type of term: " <> show term)

check :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Term Surface -> Type Surface -> m Elab
check tm ty = do
  Elab (ElabF tm' elabTy) <- infer tm
  ty' <- erase <$> check ty (Term (Core Type))
  equate ty' elabTy
  pure (Elab (ElabF tm' ty'))


identity :: Term Surface
identity = Term (Core (Abs "x" (Term (Core (Var "x")))))

constant :: Term Surface
constant = Term (Core (Abs "x" (Term (Core (Abs "y" (Term (Core (Var "x"))))))))


class Functor f => Recursive f t | t -> f where
  project :: t -> f t

cata :: Recursive f t => (f a -> a) -> t -> a
cata algebra = go
  where go = algebra . fmap go . project
