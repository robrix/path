{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Expr where

import Control.Monad (unless)
import Data.Function (on)

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Eq, Ord, Show)

data Core a
  = Bound Int
  | Free Name
  | Lam a
  | a :@ a
  | Type
  | Pi a a
  deriving (Eq, Functor, Ord, Show)

data Surface a
  = Core (Core a)
  | Ann a (Term Surface)
  deriving (Eq, Functor, Ord, Show)

(-->) :: Term Surface -> Term Surface -> Term Surface
a --> b = Term (Core (Pi a b))

infixr 0 -->

typeT :: Term Surface
typeT = Term (Core Type)

tvar :: Int -> Term Surface
tvar = Term . Core . Bound

newtype Term f = Term (f (Term f))

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)
deriving instance Show (f (Term f)) => Show (Term f)

type Type = Value

newtype Elab = Elab { unElab :: ElabF Core Elab }
  deriving (Eq, Ord, Show)

data ElabF f a = ElabF { elabFExpr :: f a, elabFType :: Type }
  deriving (Eq, Functor, Ord, Show)

instance Recursive (ElabF Core) Elab where project = unElab

elab :: Core Elab -> Type -> Elab
elab = fmap Elab . ElabF

elabType :: Elab -> Type
elabType = elabFType . unElab

erase :: Elab -> Term Core
erase = cata (Term . elabFExpr)

data Value
  = VLam (Value -> Value)
  | VType
  | VPi Value (Value -> Value)
  | VNeutral Neutral

instance Eq Value where
  (==) = (==) `on` quote

instance Ord Value where
  compare = compare `on` quote

instance Show Value where
  showsPrec d = showsPrec d . quote

vfree :: Name -> Value
vfree = VNeutral . NFree

data Neutral
  = NFree Name
  | NApp Neutral Value
  deriving (Eq, Ord, Show)

quote :: Value -> Term Core
quote = quote' 0

quote' :: Int -> Value -> Term Core
quote' _ VType = Term Type
quote' i (VLam f) = Term (Lam (quote' (succ i) (f (vfree (Quote i)))))
quote' i (VPi t f) = Term (Pi (quote' i t) (quote' (succ i) (f (vfree (Quote i)))))
quote' i (VNeutral n) = quoteN i n

quoteN :: Int -> Neutral -> Term Core
quoteN i (NFree n) = boundFree i n
quoteN i (NApp n a) = Term (quoteN i n :@ quote' i a)

boundFree :: Int -> Name -> Term Core
boundFree i (Quote k) = Term (Bound (i - k - 1))
boundFree _ n = Term (Free n)

type Env = [Value]

eval :: Term Core -> Env -> Value
eval (Term (Bound i)) d = d !! i
eval (Term (Free name)) _ = vfree name
eval (Term (Lam b)) d = VLam (eval b . (: d))
eval (Term (f :@ a)) d = eval f d `vapp` eval a d
eval (Term Type) _ = VType
eval (Term (Pi ty body)) d = VPi (eval ty d) (eval body . (: d))

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)


subst :: Int -> Term Surface -> Term Surface -> Term Surface
subst i r (Term (Ann e t)) = Term (Ann (subst i r e) (subst i r t))
subst i r (Term (Core (Bound j)))
  | i == j    = r
  | otherwise = Term (Core (Bound j))
subst _ _ (Term (Core (Free n))) = Term (Core (Free n))
subst i r (Term (Core (Lam b))) = Term (Core (Lam (subst (succ i) r b)))
subst i r (Term (Core (f :@ a))) = Term (Core (subst i r f :@ subst i r a))
subst _ _ (Term (Core Type)) = Term (Core Type)
subst i r (Term (Core (Pi t t'))) = Term (Core (Pi (subst i r t) (subst (succ i) r t')))

type Context = [(Name, Value)]

type Result = Either String

infer :: Context -> Term Surface -> Result Elab
infer = infer' 0

infer' :: Int -> Context -> Term Surface -> Result Elab
infer' i ctx (Term (Ann e t)) = do
  t' <- check' i ctx t VType
  let t'' = eval (erase t') []
  check' i ctx e t''
infer' _ _ (Term (Core Type)) = pure (elab Type VType)
infer' i ctx (Term (Core (Pi t b))) = do
  t' <- check' i ctx t VType
  let t'' = eval (erase t') []
  b' <- check' (succ i) ((Local i, t'') : ctx) (subst 0 (Term (Core (Free (Local i)))) b) VType
  pure (elab (Pi t' b') VType)
infer' _ ctx (Term (Core (Free n))) = maybe (Left ("free variable: " <> show n)) (pure . elab (Free n)) (lookup n ctx)
infer' i ctx (Term (Core (f :@ a))) = do
  f' <- infer' i ctx f
  case elabType f' of
    VPi t t' -> do
      a' <- check' i ctx a t
      pure (elab (f' :@ a') (t' (eval (erase a') [])))
    _ -> Left ("illegal application of " <> show f')
infer' _ _ tm = Left ("no rule to infer type of " <> show tm)

check' :: Int -> Context -> Term Surface -> Type -> Result Elab
check' i ctx (Term (Core (Lam e))) (VPi t t') = check' (succ i) ((Local i, t) : ctx) (subst 0 (Term (Core (Free (Local i)))) e) (t' (vfree (Local i)))
check' i ctx tm ty = do
  v <- infer' i ctx tm
  unless (elabType v == ty) (Left ("type mismatch: " <> show v <> " vs. " <> show ty))
  pure v


identity :: Term Surface
identity = Term (Core (Lam (Term (Core (Bound 0)))))

constant :: Term Surface
constant = Term (Core (Lam (Term (Core (Lam (Term (Core (Bound 1))))))))


class Functor f => Recursive f t | t -> f where
  project :: t -> f t

cata :: Recursive f t => (f a -> a) -> t -> a
cata algebra = go
  where go = algebra . fmap go . project
