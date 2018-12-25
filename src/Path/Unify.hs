{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, TupleSections #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad ((<=<), unless)
import Data.Foldable (toList)
import Data.Monoid (Any(..))
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
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
  = N Var (Back Elim)
  | L (Bind QName Term)
  | Set
  | Type
  | Pi Type (Bind QName Type)
  deriving (Eq, Ord, Show)

newtype Elim = A Term
  deriving (Eq, Ord, Show)

data Flavour = Vars | RigVars | Metas

class Occurs t where
  free   :: Flavour -> t -> Set QName

fvs, fvrigs, fmvs :: Occurs t => t -> Set QName
fvs       = free Vars
fvrigs    = free RigVars
fmvs      = free Metas

instance Occurs Term where
    free l       (L b)         = free l b
    free _       Set           = mempty
    free _       Type          = mempty
    free l       (Pi _S _T)    = free l _S <> free l _T
    free RigVars (N (V x _) e) = Set.singleton x <> free RigVars e
    free RigVars (N (M _) _)   = mempty
    free l       (N h e)       = free l h <> free l e

instance Occurs Var where
    free Vars    (M _)     = mempty
    free RigVars (M _)     = mempty
    free Metas   (M alpha) = Set.singleton alpha
    free Vars    (V x _)   = Set.singleton x
    free RigVars (V x _)   = Set.singleton x
    free Metas   (V _ _)   = mempty

instance Occurs Elim where
   free l (A a)        = free l a

(<?) :: Occurs t => QName -> t -> Bool
x <? t = x `Set.member` (fmvs t <> fvs t)

instance Occurs t => Occurs [t] where
    free l = Set.unions . map (free l)

instance Occurs t => Occurs (Back t) where
    free l = free l . toList

instance (Occurs s, Occurs t) => Occurs (s, t) where
    free l (s, t) = free l s <> free l t

instance (Occurs s, Occurs t, Occurs u) => Occurs (s, t, u) where
    free l (s, t, u) = Set.unions [free l s, free l t, free l u]

instance (Occurs s, Occurs t, Occurs u, Occurs v) => Occurs (s, t, u, v) where
    free l (s, t, u, v) = Set.unions [free l s, free l t, free l u, free l v]

instance Occurs t => Occurs (Bind QName t) where
    free l (B v t) = Set.delete v (free l t)

type Type = Term

data Bind p t = B p t
  deriving (Eq, Ord, Show)

type Subs = [(QName, Term)]

bind :: a -> b -> Bind a b
bind = B

unbind :: (Carrier sig m, Member Fresh sig, Monad m) => Bind a b -> m (a, b)
unbind (B p t) = pure (p, t)

unbind2 :: Applicative m => Bind a b -> Bind c d -> m (Maybe (a, b, c, d))
unbind2 (B p1 t1) (B p2 t2) = pure (Just (p1, t1, p2, t2))

unsafeUnbind :: Bind a b -> (a, b)
unsafeUnbind (B p t) = (p, t)

h :: Var -> Term
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

inst :: Bind QName Term -> Term -> Term
inst f s = L f $$ s

(%%) :: Term -> Elim -> Term
L b   %% A a = eval [(x, a)] t where (x, t) = unsafeUnbind b
N h e %% z   = N h (e :> z)
_     %% _   = error "bad elimination"

eval :: Subs -> Term -> Term
eval g (L b)        = L (evalUnder g b)
eval g (N h e)      = foldl (%%) (evalHead g h) (fmap (mapElim (eval g)) e)
eval _ Set          = Set
eval _ Type         = Type
eval g (Pi _S _T)   = Pi (eval g _S) (evalUnder g _T)

evalHead :: Subs -> Var -> Term
evalHead g (V x _)    | Just t <- lookup x g      = t
evalHead g (M alpha)  | Just t <- lookup alpha g  = t
evalHead _ h                                      = N h Nil

evalUnder :: Subs -> Bind QName Term -> Bind QName Term
evalUnder g b = bind x (eval g t)
                  where (x, t) = unsafeUnbind b

mapElim :: (Term -> Term) -> Elim -> Elim
mapElim f (A a) = A (f a)

foldMapElim :: (Term -> m) -> Elim -> m
foldMapElim f (A a) = f a

data Equation = (Term, Type) :==: (Term, Type)
  deriving (Eq, Ord, Show)

instance Occurs Equation where
  free l ((s, _S) :==: (t, _T)) = free l (_S, s, _T, t)

sym :: Equation -> Equation
sym (s :==: t) = t :==: s

data Param = P Type | Type :++: Type
  deriving (Eq, Ord, Show)

instance Occurs Param where
  free l (P _T)       = free l _T
  free l (_S :++: _T) = free l _S <> free l _T

type Params = Back (QName, Param)

data Dec a = Hole | Defn a
  deriving (Eq, Ord, Show)

instance Occurs v => Occurs (Dec v) where
  free _ Hole     = mempty
  free l (Defn t) = free l t

data Entry
  = E QName Type (Dec Term)
  | Q Status Problem
  deriving (Eq, Ord, Show)

instance Occurs Entry where
  free l (E _ t d) = free l t <> free l d
  free l (Q _ p)   = free l p

data Status = Blocked | Active
  deriving (Eq, Ord, Show)

data Problem
  = Unify Equation
  | All Param (Bind QName Problem)
  deriving (Eq, Ord, Show)

instance Occurs Problem where
  free l (Unify q) = free l q
  free l (All e b) = free l (e, b)


type Telescope = Back (QName, Type)

telescope :: (Carrier sig m, Member (Error String) sig, Member Fresh sig, Monad m) => Type -> m (Telescope, Type)
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

pushLs :: (Carrier sig m, Member (State ContextL) sig, Monad m, Traversable f) => f Entry -> m ()
pushLs es = traverse pushL es >> pure ()


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

inScope :: (Carrier sig m, Member (Reader Params) sig) => QName -> Param -> m a -> m a
inScope x p = localParams (:> (x, p))

lookupVar :: (Carrier sig m, Member (Reader Params) sig, Monad m) => QName -> Twin -> m Type
lookupVar x w = ask >>= go w
  where go Only  (_ :> (y, P t))      | x == y = pure t
        go TwinL (_ :> (y, s :++: _)) | x == y = pure s
        go TwinR (_ :> (y, _ :++: t)) | x == y = pure t
        go w     (c :> _)                      = go w c
        go _     Nil                           = error $ "lookupVar: missing " <> show x -- FIXME: free variable error or something?


freshName :: (Applicative m, Carrier sig m, Member Fresh sig, Member (Reader ModuleName) sig) => m QName
freshName = mk <$> ask <*> fresh
  where mk m i = m :.: Gensym i


postpone :: (Carrier sig m, Member (Reader Params) sig, Member (State ContextR) sig, Monad m) => Status -> Problem -> m ()
postpone s p = ask >>= pushR . Right . Q s . wrapProb p
  where wrapProb :: Problem -> Params -> Problem
        wrapProb = foldr (\ (x, e) p -> All e (bind x p))

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


flexTerm :: (Carrier sig m, Member (Error String) sig, Member Fresh sig, Member (Reader Params) sig, Member (State ContextL) sig, Member (State ContextR) sig, Monad m) => [Entry] -> Equation -> m ()
flexTerm _Xi q@((N (M alpha) _, _) :==: _) = do
  _Gam <- fmap snd <$> askParams
  popL >>= \ e -> case e of
    E beta _T Hole
      | alpha == beta && alpha `elem` fmvs _Xi   -> do  pushLs (e:_Xi)
                                                        block (Unify q)
      | alpha == beta                            -> do  pushLs _Xi
                                                        tryInvert q _T
                                                            <|| (block (Unify q) >> pushL e)
      | beta `elem` fmvs (_Gam, _Xi, q)          ->  flexTerm (e : _Xi) q
    _                                            -> do  pushR (Right e)
                                                        flexTerm _Xi q

tryInvert :: (Carrier sig m, Member (Error String) sig, Member Fresh sig, Member (Reader Params) sig, Member (State ContextL) sig, Member (State ContextR) sig, Monad m) => Equation -> Type -> m Bool
tryInvert q@((N (M alpha) e, _) :==: (s, _)) _T = invert alpha _T e s >>= \ m -> case m of
        Nothing  ->  pure False
        Just v   ->  do  active (Unify q)
                         define Nil alpha _T v
                         pure True
tryInvert _ q = error $ "tryInvert: " ++ show q


invert :: (Carrier sig m, Member (Error String) sig, Member Fresh sig, Member (Reader Params) sig, Member (State ContextL) sig, Monad m) => QName -> Type -> Back Elim -> Term -> m (Maybe Term)
invert alpha _T e t  | occurCheck True alpha t = throwError "occur check"
                     | alpha `Set.notMember` fmvs t, Just xs <- toVars e, linearOn t xs = do
                         b <- localParams (const Nil) (typecheck _T (lams xs t))
                         pure $ if b then Just (lams xs t) else Nothing
                     | otherwise = pure Nothing

occurCheck :: Bool -> QName -> Term -> Bool
occurCheck w alpha (L b)           =  occurCheck w alpha t
                                          where (_, t) = unsafeUnbind b
occurCheck _ alpha (N (V _ _) e)   =  getAny $ foldMap
                                          (foldMapElim (Any . occurCheck False alpha)) e
occurCheck w alpha (N (M beta) e)  =  alpha == beta && (w || isJust (toVars e))
occurCheck _ _     Set             =  False
occurCheck _ _     Type            =  False
occurCheck w alpha (Pi _S _T)      =  occurCheck w alpha _S || occurCheck w alpha _T'
                                          where (_, _T') = unsafeUnbind _T

linearOn :: Term -> Back QName -> Bool
linearOn _  Nil       = True
linearOn t  (as:>a)  = not (a `elem` fvs t && a `elem` as) && linearOn t as

etaContract :: Term -> Term
etaContract (L b) = case etaContract t of
     N x (e :> A (N (V y' _) Nil)) | y == y', not (y `elem` fvs e)  -> N x e
     t'                                                            -> lam y t'
   where (y, t) = unsafeUnbind b
etaContract (N x as)    = N x (fmap (mapElim etaContract) as)
etaContract Set       = Set
etaContract Type       = Type

toVar :: Term -> Maybe QName
toVar v = case etaContract v of  N (V x _) Nil  -> Just x
                                 _             -> Nothing

toVars :: Traversable f => f Elim -> Maybe (f QName)
toVars = traverse (toVar <=< unA)
  where  unA (A t)  = Just t


equal :: (Carrier sig m, Member (Error String) sig, Member Fresh sig, Member (Reader Params) sig, Member (State ContextL) sig, Monad m) => Type -> Term -> Term -> m Bool
equal _T s t =  (equalise _T s t >> pure True) `catchError` \ s -> (s :: String) `seq` pure False

typecheck :: (Carrier sig m, Member (Error String) sig, Member Fresh sig, Member (Reader Params) sig, Member (State ContextL) sig, Monad m) => Type -> Term -> m Bool
typecheck _T t = equal _T t t

equalise :: (Carrier sig m, Member (Error String) sig, Member Fresh sig, Member (Reader Params) sig, Member (State ContextL) sig, Monad m) => Type -> Term -> Term -> m Term
equalise Type  Set   Set   = pure Set
equalise Type  _S    _T    = equalise Set _S _T
equalise Set   (Pi _A _B) (Pi _S _T) = do
    _U <- equalise Set _A _S
    Pi _U <$>   bindsInScope _U _B _T
                   (\ _ -> equalise Set)
equalise (Pi _U _V) f g =
    L <$>  bindInScope _U _V
               (\ x _V' -> equalise _V' (f $$ var x) (g $$ var x))
equalise _U (N h e) (N h' e') = do
    (h'', e'', _V) <- equaliseN h e h' e'
    _ <- equalise Type _U _V
    pure (N h'' e'')

equalise _U s t = throwError $ "Type " ++ show _U ++ " does not make "
                         ++ show s ++ " equal to " ++ show t


equaliseN :: (Carrier sig m, Member (Error String) sig, Member Fresh sig, Member (Reader Params) sig, Member (State ContextL) sig, Monad m) => Var -> Back Elim -> Var -> Back Elim ->
                  m (Var, Back Elim, Type)
equaliseN h Nil h' Nil | h == h'          = (h, Nil,) <$> infer h
equaliseN h (e :> A s)  h' (e' :> A t)  = do
    (h'', e'', Pi _U _V)  <- equaliseN h e h' e'
    u                     <- equalise _U s t
    return (h'', e'' :> A u, inst _V u)
equaliseN h e h' e' = throwError $ "Neutral terms " ++ show h ++ " . " ++ show e
                              ++ " and " ++ show h' ++ " . " ++ show e'
                              ++ " not equal!"

infer :: (Carrier sig m, Member (Reader Params) sig, Member (State ContextL) sig, Monad m) => Var -> m Type
infer (V x w)  = lookupVar x w
infer (M x)    = lookupMeta x

bindInScope :: (Carrier sig m, Member Fresh sig, Member (Reader Params) sig, Monad m) => Type -> Bind QName Term ->
                  (QName -> Term -> m Term) ->
                  m (Bind QName Term)
bindInScope _T b f = do  (x, b') <- unbind b
                         bind x <$> inScope x (P _T) (f x b')

bindsInScope :: (Carrier sig m, Member (Error String) sig, Member Fresh sig, Member (Reader Params) sig, Monad m) => Type -> Bind QName Term -> Bind QName Term ->
                   (QName -> Term -> Term -> m Term) ->
                   m (Bind QName Term)
bindsInScope _T a b f = do  Just (x, a', _, b') <- unbind2 a b
                            bind x <$> inScope x (P _T) (f x a' b')
