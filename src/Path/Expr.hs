{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Expr where

import Data.Function (fix, on)

data Name
  = Global String
  | Local String
  | Quote String
  deriving (Eq, Ord, Show)

data Core a
  = Bound String
  | Free Name
  | Lam String a
  | a :@ a
  | Type
  | Pi String a a
  deriving (Eq, Functor, Ord, Show)

data Surface a
  = Core (Core a)
  | Ann a (Term Surface)
  deriving (Eq, Functor, Ord, Show)

(-->) :: (String, Term Surface) -> Term Surface -> Term Surface
(n, a) --> b = Term (Core (Pi n a b))

infixr 0 -->

typeT :: Term Surface
typeT = Term (Core Type)

global :: String -> Term Surface
global = Term . Core . Free . Global

var :: String -> Term Surface
var = Term . Core . Bound

lam :: String -> Term Surface -> Term Surface
lam n = Term . Core . Lam n

(.:)  :: Term Surface -> Term Surface -> Term Surface
a .: t = Term (Ann a t)

(#) :: Term Surface -> Term Surface -> Term Surface
f # a = Term (Core (f :@ a))


newtype Term f = Term (f (Term f))

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)

fresh :: [String] -> String
fresh [] = "a"
fresh (s:_) = prime s

prime :: String -> String
prime [c] | c < 'z' = [succ c]
prime s = s <> "ʹ"

showVar :: [String] -> Int -> ShowS
showVar vs i | i < length vs = showString (vs !! i)
             | otherwise     = showChar '_' . shows i

showCore :: ([String] -> Int -> x -> ShowS) -> [String] -> Int -> Core x -> ShowS
showCore go vs d c = case c of
  Bound s -> showString s
  Free (Global s) -> showString s
  Free (Local s) -> showString s
  Free (Quote s) -> showChar '\'' . showString s
  Lam v b -> showParen (d > 0) $ showString "\\ " . showString v . showString " -> " . go (v : vs) 0 b
  f :@ a -> showParen (d > 10) $ go vs 10 f . showChar ' ' . go vs 11 a
  Type -> showString "Type"
  Pi v t b -> showParen (d > 1) $ showBrace True (showString v . showString " : " . go vs 0 t) . showString " -> " . go (v : vs) 1 b

showBrace :: Bool -> ShowS -> ShowS
showBrace True s = showChar '{' . s . showChar '}'
showBrace False s = s

showCoreTerm :: [String] -> Int -> Term Core -> ShowS
showCoreTerm = fix (\ f vs d (Term core) -> showCore f vs d core)

showType :: [String] -> Int -> Type -> ShowS
showType vs d = showCoreTerm vs d . quote 0

instance Show (Term Surface) where
  showsPrec = fix (\ f vs d (Term surface) -> case surface of
    Core core -> showCore f vs d core
    Ann e t -> showParen (d > 0) $ f vs 1 e . showString " : " . f vs 0 t) []

instance Show (Term Core) where
  showsPrec = showCoreTerm []


type Type = Value

data Value
  = VLam (Value -> Value)
  | VType
  | VPi Value (Value -> Value)
  | VNeutral Neutral

instance Eq Value where
  (==) = (==) `on` quote 0

instance Ord Value where
  compare = compare `on` quote 0

instance Show Value where
  showsPrec d = showsPrec d . quote 0

vfree :: Name -> Value
vfree = VNeutral . NFree

data Neutral
  = NFree Name
  | NApp Neutral Value
  deriving (Eq, Ord, Show)

prettyVar :: Int -> String
prettyVar d = let (n, i) = d `divMod` 26 in replicate (succ n) (alphabet !! i)
  where alphabet = ['a'..'z']

quote :: Int -> Value -> Term Core
quote _ VType = Term Type
quote i (VLam f) = let v = prettyVar i in Term (Lam v (quote (succ i) (f (vfree (Quote v)))))
quote i (VPi t f) = let v = prettyVar i in Term (Pi v (quote i t) (quote (succ i) (f (vfree (Quote v)))))
quote i (VNeutral n) = quoteN i n

quoteN :: Int -> Neutral -> Term Core
quoteN _ (NFree (Quote s)) = Term (Bound s)
quoteN _ (NFree n) = Term (Free n)
quoteN i (NApp n a) = Term (quoteN i n :@ quote i a)

subst :: String -> Term Surface -> Term Surface -> Term Surface
subst i r (Term (Ann e t)) = Term (Ann (subst i r e) (subst i r t))
subst i r (Term (Core (Bound j)))
  | i == j    = r
  | otherwise = Term (Core (Bound j))
subst _ _ (Term (Core (Free n))) = Term (Core (Free n))
subst i r (Term (Core (Lam n b)))
  | i == n    = Term (Core (Lam n b))
  | otherwise = Term (Core (Lam n (subst i r b)))
subst i r (Term (Core (f :@ a))) = Term (Core (subst i r f :@ subst i r a))
subst _ _ (Term (Core Type)) = Term (Core Type)
subst i r (Term (Core (Pi n t t')))
  | i == n    = Term (Core (Pi n (subst i r t) t'))
  | otherwise = Term (Core (Pi n (subst i r t) (subst i r t')))


identity :: Term Surface
identity = lam "0" (var "0")

constant :: Term Surface
constant = lam "1" (lam "0" (var "1"))


class Functor f => Recursive f t | t -> f where
  project :: t -> f t

cata :: Recursive f t => (f a -> a) -> t -> a
cata algebra = go
  where go = algebra . fmap go . project
