{-# LANGUAGE DeriveTraversable, FlexibleContexts #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Fresh
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad (unless)
import Control.Monad.Fail
import Path.Name hiding (Assoc(..))

data Back a = Nil | Back a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Semigroup (Back a) where
  as  <> Nil     = as
  Nil <> bs      = bs
  as  <> bs :> b = (as <> bs) :> b

instance Monoid (Back a) where
  mempty = Nil
  mappend = (<>)

data Term
  = N Head (Back Elim)
  | L (Bind QName Term)
  | Set
  | Pi Type (Bind QName Type)
  deriving (Eq, Ord, Show)

newtype Elim = A Term
  deriving (Eq, Ord, Show)

type Type = Term

data Twin = Only | TwinL | TwinR
  deriving (Eq, Ord, Show)

data Head = V QName Twin | M QName
  deriving (Eq, Ord, Show)

type Bind = (,)

type Subs = [(QName, Term)]

bind :: a -> b -> Bind a b
bind = (,)

unbind :: Applicative m => Bind a b -> m (a, b)
unbind = pure

h :: Head -> Term
h h = N h Nil

twin :: QName -> Twin -> Term
twin q w = h (V q w)

twinL :: QName -> Term
twinL q = twin q TwinL

twinR :: QName -> Term
twinR q = twin q TwinL

var :: QName -> Term
var q = twin q Only

meta :: QName -> Term
meta q = h (M q)

($$) :: Term -> Term -> Term
f $$ a = f %% A a

($*$) :: Term -> Back (QName, Type) -> Term
f $*$ _Gam = foldl ($$) f (fmap (var . fst) _Gam)

(%%) :: Term -> Elim -> Term
L b   %% A a = eval [(x, a)] t where (x, t) = b
N h e %% z   = N h (e :> z)
_     %% _   = error "bad elimination"

eval :: Subs -> Term -> Term
eval g (L b)        = L (evalUnder g b)
eval g (N h e)      = foldl (%%) (evalHead g h) (fmap (mapElim (eval g)) e)
eval _ Set          = Set
eval g (Pi _S _T)   = Pi (eval g _S) (evalUnder g _T)

evalHead :: Subs -> Head -> Term
evalHead g (V x _)    | Just t <- lookup x g      = t
evalHead g (M alpha)  | Just t <- lookup alpha g  = t
evalHead _ h                                      = N h Nil

evalUnder :: Subs -> Bind QName Term -> Bind QName Term
evalUnder g b = bind x (eval g t)
                  where (x, t) = b

mapElim :: (Term -> Term) -> Elim -> Elim
mapElim f (A a) = A (f a)

foldMapElim :: (Term -> m) -> Elim -> m
foldMapElim f (A a) = f a

data Equation = (Term, Type) :==: (Term, Type)
  deriving (Eq, Ord, Show)

sym :: Equation -> Equation
sym (s :==: t) = t :==: s

data Param = P Type | Type :++: Type
  deriving (Eq, Ord, Show)

type Params = Back (QName, Param)

data Dec a = Hole | Defn a
  deriving (Eq, Ord, Show)

data Entry
  = E QName Type (Dec Term)
  | Q Status Problem
  deriving (Eq, Ord, Show)

data Status = Blocked | Active
  deriving (Eq, Ord, Show)

data Problem
  = Unify Equation
  | All Param QName Problem
  deriving (Eq, Ord, Show)


type Telescope = Back (QName, Type)

telescope :: MonadFail m => Type -> m (Telescope, Type)
telescope (Pi s t) = do
  (x, t') <- unbind t
  (tel, u) <- telescope t'
  pure ((Nil :> (x, s)) <> tel, u)
telescope t        = pure (Nil, t)

lam :: QName -> Term -> Term
lam x t = L (bind x t)

lams :: Foldable f => f QName -> Term -> Term
lams xs t = foldr lam t xs

lams' :: (Functor f, Foldable f) => f (QName, Type) -> Term -> Term
lams' xs t = lams (fmap fst xs) t

_Pi :: QName -> Type -> Type -> Type
_Pi x _S _T = Pi _S (bind x _T)

_Pis :: Foldable f => f (QName, Type) -> Type -> Type
_Pis xs _T = foldr (uncurry _Pi) _T xs


type ContextL = Back Entry
type ContextR = [Either Subs Entry]

popL :: (Carrier sig m, Member (State ContextL) sig, Monad m) => m Entry
popL = do
  entries <- get
  case entries of
    es :> e -> e <$ put es
    Nil     -> error "popL: empty context"

pushL :: (Carrier sig m, Member (State ContextL) sig, Monad m) => Entry -> m ()
pushL e = modify (:> e)


popR :: (Carrier sig m, Member (State ContextR) sig, Monad m) => m (Maybe (Either Subs Entry))
popR = do
  entries <- get
  case entries of
    e : es -> Just e <$ put es
    []     -> pure Nothing

pushR :: (Carrier sig m, Member (State ContextR) sig, Monad m) => Either Subs Entry -> m ()
pushR e = modify (e:)

lookupMeta :: (Carrier sig m, Member (State ContextL) sig, Monad m) => QName -> m Type
lookupMeta x = get >>= go
  where go (_   :> E y _T _) | x == y = pure _T
        go (mcx :> _)                 = go mcx
        go Nil                        = error $ "lookupMeta: missing " <> show x


goLeft :: (Carrier sig m, Member (State ContextL) sig, Member (State ContextR) sig, Monad m) => m ()
goLeft = popL >>= pushR . Right


askParams :: (Carrier sig m, Member (Reader Params) sig) => m Params
askParams = ask

localParams :: (Carrier sig m, Member (Reader Params) sig) => (Params -> Params) -> m a -> m a
localParams = local

lookupVar :: (Carrier sig m, Member (Reader Params) sig, Monad m) => QName -> Twin -> m Type
lookupVar x w = ask >>= go w
  where go Only  (_ :> (y, P t))      | x == y = return t
        go TwinL (_ :> (y, s :++: _)) | x == y = return s
        go TwinR (_ :> (y, _ :++: t)) | x == y = return t
        go w     (c :> _)                      = go w c
        go _     Nil                           = error $ "lookupVar: missing " <> show x -- FIXME: free variable error or something?


freshName :: (Applicative m, Carrier sig m, Member Fresh sig, Member (Reader ModuleName) sig) => m QName
freshName = mk <$> ask <*> fresh
  where mk m i = m :.: Gensym i


postpone :: (Carrier sig m, Member (Reader Params) sig, Member (State ContextR) sig, Monad m) => Status -> Problem -> m ()
postpone s p = ask >>= pushR . Right . Q s . wrapProb p
  where wrapProb :: Problem -> Params -> Problem
        wrapProb = foldr (\ (x, e) p -> All e x p)

active, block :: (Carrier sig m, Member (Reader Params) sig, Member (State ContextR) sig, Monad m) => Problem -> m ()
active = postpone Active
block  = postpone Blocked


hole :: (Carrier sig m, Member Fresh sig, Member (Reader ModuleName) sig, Member (State ContextL) sig, Member (State ContextR) sig, Monad m) => Telescope -> Type -> (Term -> m a) -> m a
hole gam t f = do
  alpha <- freshName
  pushL $ E alpha (_Pis gam t) Hole
  r <- f (meta alpha $*$ gam)
  r <$ goLeft

define :: (Carrier sig m, Member (State ContextR) sig, Monad m) => Telescope -> QName -> Type -> Term -> m ()
define _Gam alpha _S v = do  pushR $ Left [(alpha, t)]
                             pushR $ Right $ E alpha _T (Defn t)
  where  _T  = _Pis _Gam _S
         t   = lams' _Gam v

(<||) :: Monad m => m Bool -> m () -> m ()
a <|| b = do  x <- a
              unless x b

infixr 5 <||
