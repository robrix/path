{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Expr where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader
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

instance Functor f => Recursive (TypeF f) (Type f) where project = unType

freeTypeVariables :: Type Core -> Set.Set Name
freeTypeVariables = cata $ \ ty -> case ty of
  TypeT -> mempty
  Pi n t b -> t <> Set.delete n b
  Expr (Var n) -> Set.singleton n
  Expr (Abs n b) -> Set.delete n b
  Expr (App f a) -> f <> a

aeq :: Type Core -> Type Core -> Bool
aeq t1 t2 = run (runReader ([] :: [(Name, Name)]) (aeq' t1 t2))

aeq' :: (Carrier sig m, Member (Reader [(Name, Name)]) sig, Monad m) => Type Core -> Type Core -> m Bool
aeq' (Type TypeT) (Type TypeT) = pure True
aeq' (Type (Pi n1 t1 b1)) (Type (Pi n2 t2 b2)) = do
  t <- t1 `aeq'` t2
  if t then
    if n1 == n2 then
      b1 `aeq'` b2
    else do
      let n = fresh (freeTypeVariables b1 <> freeTypeVariables b2)
      local (((n1, n) :) . ((n2, n) :)) (b1 `aeq'` b2)
  else
    pure False
aeq' (Type (Expr (Var n1))) (Type (Expr (Var n2))) = do
  env <- ask
  pure (fromMaybe n1 (lookup n1 env) == fromMaybe n2 (lookup n2 env))
aeq' (Type (Expr (Abs n1 b1))) (Type (Expr (Abs n2 b2))) = do
  if n1 == n2 then
    b1 `aeq'` b2
  else do
    let n = fresh (freeTypeVariables b1 <> freeTypeVariables b2)
    local (((n1, n) :) . ((n2, n) :)) (b1 `aeq'` b2)
aeq' (Type (Expr (App f1 a1))) (Type (Expr (App f2 a2))) = do
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

data ValT
  = VTypeT
  | VClosureT Name (Type Core) Context
  deriving (Eq, Ord, Show)

quoteType :: ValT -> Type Core
quoteType VTypeT = Type TypeT
quoteType (VClosureT n b _) = Type (Expr (Abs n b))

evalType :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Type Core -> m ValT
evalType (Type TypeT) = pure VTypeT
evalType (Type (Pi n _ b)) = VClosureT n b <$> ask
evalType (Type (Expr (Var n))) = asks (lookup n) >>= maybe (fail ("free variable: " <> n)) pure >>= evalType
evalType (Type (Expr (Abs n b))) = VClosureT n b <$> ask
evalType (Type (Expr (App f a))) = do
  f' <- evalType f
  case f' of
    VClosureT n b c ->
      local (const ((n, a) : c)) (evalType b)
    v -> fail ("attempting to apply " <> show v)


equate :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Type Core -> Type Core -> m ()
equate ty1 ty2 | ty1 `aeq` ty2 = pure ()
               | otherwise     = do
  ty1' <- evalType ty1
  ty2' <- evalType ty2
  if quoteType ty1' `aeq` quoteType ty2' then
    pure ()
  else
    fail ("could not judge " <> show ty1 <> " = " <> show ty2)

infer :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Term Surface -> m Elab
infer (Term (Core (Var name))) = do
  ty <- asks (lookup name) >>= maybe (fail ("free variable: " <> name)) pure
  pure (Elab (ElabF (Var name) ty))
infer (Term (Ann tm ty)) = check tm ty
infer term = fail ("no rule to infer type of term: " <> show term)

check :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Term Surface -> Type Surface -> m Elab
check tm ty = do
  Elab (ElabF tm' elabTy) <- infer tm
  ty' <- inferType ty
  if ty' `aeq` elabTy then
    pure (Elab (ElabF tm' ty'))
  else
    fail ("could not judge " <> show ty' <> " = " <> show elabTy)


inferType :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Type Surface -> m (Type Core)
inferType (Type TypeT) = pure (Type TypeT)
inferType (Type (Expr (Core (Var name)))) = asks (lookup name) >>= maybe (fail ("free variable: " <> name)) pure
inferType ty = fail ("no rule to infer type of type: " <> show ty)


identity :: Term Surface
identity = Term (Core (Abs "x" (Term (Core (Var "x")))))

constant :: Term Surface
constant = Term (Core (Abs "x" (Term (Core (Abs "y" (Term (Core (Var "x"))))))))


class Functor f => Recursive f t | t -> f where
  project :: t -> f t

cata :: Recursive f t => (f a -> a) -> t -> a
cata algebra = go
  where go = algebra . fmap go . project
