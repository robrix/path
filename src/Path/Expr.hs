{-# LANGUAGE FlexibleContexts, FunctionalDependencies #-}
module Path.Expr where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader
import Prelude hiding (fail)

type Name = String

data Expr a
  = Var Name
  | Abs Name a
  | App a a
  deriving (Eq, Ord, Show)

newtype Term = Term { unTerm :: Expr Term }
  deriving (Eq, Ord, Show)

data Type
  = Type
  | Pi Name Type Type
  | Expr (Expr Type)
  deriving (Eq, Ord, Show)

data Elab = Elab { elabExpr :: Expr Elab, elabType :: Type }
  deriving (Eq, Ord, Show)

data Val
  = Closure Name Term Env
  deriving (Eq, Ord, Show)

type Env = [(Name, Val)]

eval :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Term -> m Val
eval (Term (Var name)) = do
  val <- asks (lookup name)
  maybe (fail ("free variable: " <> name)) pure val
eval (Term (Abs name body)) = Closure name body <$> ask
eval (Term (App f a)) = do
  Closure n b e <- eval f
  a' <- eval a
  local (const ((n, a') : e)) (eval b)


identity :: Term
identity = Term (Abs "x" (Term (Var "x")))

constant :: Term
constant = Term (Abs "x" (Term (Abs "y" (Term (Var "x")))))


class Functor f => Recursive f t | t -> f where
  project :: t -> f t
