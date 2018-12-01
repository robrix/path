{-# LANGUAGE FlexibleContexts #-}
module Path.Expr where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader
import Prelude hiding (fail)

type Name = String

data Expr
  = Var Name
  | Abs Name Expr
  | App Expr Expr
  deriving (Eq, Ord, Show)

data Val
  = Closure Name Expr Env
  deriving (Eq, Ord, Show)

type Env = [(Name, Val)]

eval :: (Carrier sig m, Member (Reader Env) sig, MonadFail m) => Expr -> m Val
eval (Var name) = do
  val <- asks (lookup name)
  maybe (fail ("free variable: " <> name)) pure val
eval (Abs name body) = Closure name body <$> ask
eval (App f a) = do
  Closure n b e <- eval f
  a' <- eval a
  local (const ((n, a') : e)) (eval b)


identity :: Expr
identity = Abs "x" (Var "x")

constant :: Expr
constant = Abs "x" (Abs "y" (Var "x"))
