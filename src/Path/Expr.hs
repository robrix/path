{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Expr where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader
import Prelude hiding (fail)

type Name = String

data Core a
  = Var Name
  | Abs Name a
  | App a a
  deriving (Eq, Functor, Ord, Show)

data Surface a
  = Core (Core a)
  | Ann a (Type Surface)
  deriving (Eq, Functor, Ord, Show)

newtype Term f = Term { unTerm :: f (Term f) }

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)
deriving instance Show (f (Term f)) => Show (Term f)

newtype Type f = Type { unType :: TypeF f (Type f) }

deriving instance Eq (f (Type f)) => Eq (Type f)
deriving instance Ord (f (Type f)) => Ord (Type f)
deriving instance Show (f (Type f)) => Show (Type f)

data TypeF f a
  = TypeT
  | Pi Name a a
  | Expr (f a)
  deriving (Eq, Functor, Ord, Show)

newtype Elab = Elab { unElab :: ElabF Core Elab }
  deriving (Eq, Ord, Show)

data ElabF f a = ElabF { elabFExpr :: f a, elabFType :: Type Core }
  deriving (Eq, Functor, Ord, Show)

instance Recursive (ElabF Core) Elab where project = unElab

erase :: Elab -> Term Core
erase = cata (Term . elabFExpr)

data Val
  = Closure Name (Term Core) Env
  deriving (Eq, Ord, Show)

type Env = [(Name, Val)]

eval :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Term Core -> m Val
eval (Term (Var name)) = do
  val <- asks (lookup name)
  maybe (fail ("free variable: " <> name)) pure val
eval (Term (Abs name body)) = Closure name body <$> ask
eval (Term (App f a)) = do
  Closure n b e <- eval f
  a' <- eval a
  local (const ((n, a') : e)) (eval b)


type Context = [(Name, Type Core)]

infer :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Term Surface -> m Elab
infer (Term (Core (Var name))) = do
  ty <- asks (lookup name) >>= maybe (fail ("free variable: " <> name)) pure
  pure (Elab (ElabF (Var name) ty))
infer term = fail ("no rule to infer type of term: " <> show term)


identity :: Term Surface
identity = Term (Core (Abs "x" (Term (Core (Var "x")))))

constant :: Term Surface
constant = Term (Core (Abs "x" (Term (Core (Abs "y" (Term (Core (Var "x"))))))))


class Functor f => Recursive f t | t -> f where
  project :: t -> f t

cata :: Recursive f t => (f a -> a) -> t -> a
cata algebra = go
  where go = algebra . fmap go . project
