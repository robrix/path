{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeOperators #-}
module Path.Problem where

import           Control.Applicative (Alternative (..), Const (..))
import           Control.Effect
import           Control.Effect.Carrier
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Sum
import           Control.Effect.Writer
import           Control.Monad.Module
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Coerce
import qualified Data.Set as Set
import           GHC.Generics (Generic1)
import           Path.Error
import           Path.Module
import           Path.Name
import           Path.Plicity (Plicit (..))
import           Path.Pretty
import           Path.Scope
import           Path.Span
import           Path.Stack as Stack
import qualified Path.Surface as Surface
import           Path.Usage
import           Prelude hiding (pi)

data Problem a
  = Var a
  | Problem ((ProblemF :+: CoreF) Problem a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Problem where
  pure = Var
  f <*> a = eiter id Problem Var (<$> a) f

instance Monad Problem where
  a >>= f = eiter id Problem Var f a

instance Carrier (ProblemF :+: CoreF) Problem where
  eff = Problem

newtype P = P { unP :: Int }
  deriving (Eq, Ord, Show)

instance Pretty (Problem (Name Gensym)) where
  pretty = snd . run . runWriter @(Set.Set Meta) . runReader (Nil @Meta) . runReader (P 0) . kcata id alg k (var . fmap Name)
    where var (Global v) = pure (pretty (Global @Meta v))
          var (Local  v) = pretty v <$ tell (Set.singleton @Meta v)
          alg = \case
            R c -> case c of
              Lam (Scope b) -> do
                (n, b') <- bind Name (withPrec 0 b)
                prec 0 (pretty (cyan backslash) <+> pretty n </> cyan dot <+> b')
              f :$ a -> do
                f' <- withPrec 10 f
                a' <- withPrec 11 a
                prec 10 (f' <+> a')
              Let v (Scope b) -> do
                v' <- withPrec 0 v
                (n, b') <- bind Meta (withPrec 0 b)
                prec 0 (magenta (pretty "let") <+> pretty (n := v') </> magenta dot <+> b')
              Type -> pure (yellow (pretty "Type"))
              Pi t (Scope b) -> do
                t' <- withPrec 1 t
                (fvs, (n, b')) <- listen (bind Name (withPrec 0 b))
                let t'' | n `Set.member` fvs = parens (pretty (n ::: t'))
                        | otherwise          = t'
                prec 0 (t'' </> arrow <+> b')
            L p -> case p of
              Ex t (Scope b) -> do
                t' <- withPrec 1 t
                (n, b') <- bind Meta (withPrec 0 b)
                prec 0 (magenta (pretty "∃") <+> pretty (n ::: t') </> magenta dot <+> b')
              p1 :===: p2 -> do
                p1' <- withPrec 1 p1
                p2' <- withPrec 1 p2
                prec 0 (flatAlt (p1' <+> eq' <+> p2') (align (space <+> p1' </> eq' <+> p2')))
          arrow = blue (pretty "→")
          eq' = magenta (pretty "≡")
          k (Z ()) = ask >>= var . Local . Stack.head
          k (S n)  = local (Stack.tail @Meta) n
          prec d' doc = do
            d <- ask
            pure (prettyParens (d > P d') doc)
          withPrec i = local (const (P i)) . getConst
          bind cons m = do
            ns <- ask
            let n = cons $ case ns of
                  _ :> Meta sym -> prime sym
                  _ :> Name sym -> prime sym
                  _ -> Gensym Nil 0
            (,) n <$> censor (Set.delete n) (local (:> n) m)


-- FIXME: represent errors explicitly in the tree
-- FIXME: represent spans explicitly in the tree
data CoreF f a
  = Lam (Scope () f a)
  | f a :$ f a
  | Let (f a) (Scope () f a)
  | Type
  | Pi (f a) (Scope () f a)
  deriving (Foldable, Functor, Generic1, HFunctor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (CoreF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (CoreF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (CoreF f a)

instance Monad f => RModule (CoreF f) f where
  Lam b   >>=* f = Lam (b >>=* f)
  g :$ a  >>=* f = (g >>= f) :$ (a >>= f)
  Let v b >>=* f = Let (v >>= f) (b >>=* f)
  Type    >>=* _ = Type
  Pi t b  >>=* f = Pi (t >>= f) (b >>=* f)

data ProblemF f a
  = Ex (f a) (Scope () f a)
  | f a :===: f a
  deriving (Foldable, Functor, Generic1, HFunctor, Traversable)

infix 3 :===:

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (ProblemF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (ProblemF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (ProblemF f a)

instance Monad f => RModule (ProblemF f) f where
  Ex t b    >>=* f = Ex (t >>= f) (b >>=* f)
  p :===: q >>=* f = (p >>= f) :===: (q >>= f)


lam :: (Eq a, Carrier sig m, Member CoreF sig) => a -> m a -> m a
lam n b = send (Lam (bind1 n b))

lams :: (Eq a, Foldable t, Carrier sig m, Member CoreF sig) => t a -> m a -> m a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Problem a -> m (a, Problem a)
unlam n (Problem (R (Lam b))) = pure (n, instantiate1 (pure n) b)
unlam _ _                     = empty

($$) :: (Carrier sig m, Member CoreF sig) => m a -> m a -> m a
f $$ a = send (f :$ a)


let' :: (Eq a, Carrier sig m, Member CoreF sig) => a := m a -> m a -> m a
let' (n := v) b = send (Let v (bind1 n b))

unlet' :: Alternative m => a -> Problem a -> m (a := Problem a, Problem a)
unlet' n (Problem (R (Let v b))) = pure (n := v, instantiate1 (pure n) b)
unlet' _ _                       = empty


type' :: (Carrier sig m, Member CoreF sig) => m a
type' = send Type

pi :: (Eq a, Carrier sig m, Member CoreF sig) => a ::: m a -> m a -> m a
pi (n ::: t) b = send (Pi t (bind1 n b))

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t, Carrier sig m, Member CoreF sig) => t (a ::: m a) -> m a -> m a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unpi n (Problem (R (Pi t b))) = pure (n ::: t, instantiate1 (pure n) b)
unpi _ _                      = empty


exists :: (Eq a, Carrier sig m, Member ProblemF sig) => a ::: m a -> m a -> m a
exists (n ::: t) b = send (Ex t (bind1 n b))

unexists :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unexists n (Problem (L (Ex t b))) = pure (n ::: t, instantiate1 (pure n) b)
unexists _ _                      = empty

(===) :: (Carrier sig m, Member ProblemF sig) => m a -> m a -> m a
p === q = send (p :===: q)

infixr 3 ===


eiter :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . (ProblemF :+: CoreF) n a -> n a)
      -> (forall a . Incr () (n a) -> m (Incr () (n a)))
      -> (a -> m b)
      -> Problem a
      -> n b
eiter var alg k = go
  where go :: forall x y . (x -> m y) -> Problem x -> n y
        go h = \case
          Var a -> var (h a)
          Problem p -> alg $ case p of
            R c -> R $ case c of
              Lam b -> Lam (foldScope k go h b)
              f :$ a -> go h f :$ go h a
              Let v b -> Let (go h v) (foldScope k go h b)
              Type -> Type
              Pi t b -> Pi (go h t) (foldScope k go h b)
            L p -> L $ case p of
              Ex t b -> Ex (go h t) (foldScope k go h b)
              p1 :===: p2 -> go h p1 :===: go h p2

kcata :: (a -> b)
      -> (forall a . (ProblemF :+: CoreF) (Const b) a -> b)
      -> (Incr () b -> a)
      -> (x -> a)
      -> Problem x
      -> b
kcata var alg k h = getConst . eiter (coerce var) (coerce alg) (coerce k) (Const . h)


type Context = Stack (Binding ::: Problem (Name Gensym))

assume :: ( Carrier sig m
          , Member (Error Doc) sig
          , Member (Reader Span) sig
          , Member (Reader Context) sig
          )
       => Name Gensym
       -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
assume v = do
  _A <- have v
  pure (Var v ::: _A)

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader Context) sig
         )
      => m (Problem (Name Gensym) ::: Problem (Name Gensym))
      -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
intro body = do
  _A <- meta type'
  x <- fresh
  _B <- ForAll x ::: _A |- meta type'
  u <- ForAll x ::: _A |- goalIs _B body
  pure (lam (Local x) u ::: pi (Local x ::: _A) _B)

(-->) :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader Context) sig
         )
      => m (Problem (Name Gensym) ::: Problem (Name Gensym))
      -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
      -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
t --> body = do
  t' <- goalIs type' t
  x <- fresh
  b' <- ForAll x ::: t' |- goalIs type' body
  pure (pi (Local x ::: t') b' ::: type')

app :: ( Carrier sig m
       , Member Naming sig
       , Member (Reader Context) sig
       )
    => m (Problem (Name Gensym) ::: Problem (Name Gensym))
    -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
    -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
app f a = do
  _A <- meta type'
  x <- fresh
  _B <- ForAll x ::: _A |- meta type'
  let _F = pi (Local x ::: _A) _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' $$ a' ::: _F $$ a')


goalIs :: ( Carrier sig m
          , Member Naming sig
          )
       => Problem (Name Gensym)
       -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
       -> m (Problem (Name Gensym))
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- meta (ty1 === ty2)
  pure (tm1 === tm2)

meta :: (Carrier sig m, Member Naming sig) => Problem (Name Gensym) -> m (Problem (Name Gensym))
meta ty = do
  n <- fresh
  pure (exists (Local n ::: ty) (pure (Local n)))

(|-) :: (Carrier sig m, Member (Reader Context) sig) => Binding ::: Problem (Name Gensym) -> m a -> m a
b |- m = local (:> b) m

infix 3 |-

bindMeta :: (Carrier sig m, Member (Reader Context) sig) => Gensym ::: Problem (Name Gensym) -> m a -> m (Binding, a)
bindMeta (e ::: t) m = Exists (e := Nothing) ::: t |- do
  a <- m
  stack <- ask @Context
  case stack of
    Nil           -> pure (Exists (e := Nothing), a)
    _ :> e' ::: _ -> pure (e', a)

solve :: (Carrier sig m, Member (State Context) sig) => Gensym := Problem (Name Gensym) -> m ()
solve (var := val) = modify (fmap @Stack (\ (b ::: t) -> (if bindingName b == Local var then Exists (var := Just val) else b) ::: (t `asTypeOf` val)))

have :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member (Reader Span) sig
        , Member (Reader Context) sig
        )
     => Name Gensym
     -> m (Problem (Name Gensym))
have n = asks (lookupBinding n) >>= maybe (freeVariable n) (pure . typedType)


spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)

elab :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member Naming sig
        , Member (Reader Span) sig
        , Member (Reader Context) sig
        )
     => Surface.Surface (Name Meta)
     -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
elab = Surface.kcata id alg bound free
  where free (Global n)       = assume (Global n)
        free (Local (Name n)) = assume (Local n)
        free (Local (Meta n)) = (pure (Local n) :::) <$> meta type'
        bound (Z _) = asks @Context (first (Var . bindingName) . Stack.head)
        bound (S m) = local @Context (Stack.drop 1) m
        alg = \case
          Surface.Lam _ b -> intro (elab' (unScope <$> b))
          f Surface.:$ (_ :< a) -> app (elab' f) (elab' a)
          Surface.Type -> pure (type' ::: type')
          Surface.Pi (_ :< _ ::: _ :@ t) b -> elab' t --> elab' (unScope <$> b)
        elab' (t :~ s) = spanIs s (getConst t)

elabDecl :: ( Carrier sig m
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (Reader ModuleName) sig
            , Member (State Context) sig
            )
         => Decl (Surface.Surface (Name Meta))
         -> m (Decl (Problem (Name Gensym)))
elabDecl (Decl name d tm ty) = namespace (show name) $ do
  ctx <- get
  ty' <- runSpanned (runReader ctx . declare . elab) ty
  def <- meta (unSpanned ty')
  moduleName <- ask
  tm' <- runSpanned (runReader (ctx :> Define (moduleName :.: name := def) ::: unSpanned ty') . define (unSpanned ty') . elab) tm
  put (ctx :> Define (moduleName :.: name := unSpanned tm') ::: unSpanned ty')
  pure (Decl name d tm' ty')

declare :: ( Carrier sig m
           , Member Naming sig
           )
        => m (Problem (Name Gensym) ::: Problem (Name Gensym))
        -> m (Problem (Name Gensym))
declare ty = goalIs type' ty

define :: ( Carrier sig m
          , Member Naming sig
          )
       => Problem (Name Gensym)
       -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
       -> m (Problem (Name Gensym))
define ty tm = goalIs ty tm


simplifyVar :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Member (State Context) sig) => Gensym -> Problem (Name Gensym) -> m (Problem (Name Gensym))
simplifyVar v t = do
  v' <- gets (lookupBinding (Local v))
  case v' of
    -- FIXME: occurs check
    Just (Exists (n := _) ::: _) -> pure (Local v) <$ solve (n := t)
    Just _ -> do
      p <- contextualize (Problem (L (pure (Local v) :===: t)))
      ask >>= unsimplifiable . pure . (p :~)
    Nothing -> freeVariable v

contextualize :: (Carrier sig m, Member (State Context) sig) => Problem (Name Gensym) -> m (Problem (Name Gensym))
contextualize = gets . go
  where go p Nil                                  = p
        go p (ctx :> Define _              ::: _) = go p ctx
        go p (ctx :> Exists (n := Nothing) ::: t) = go (exists (Local n ::: t) p) ctx
        go p (ctx :> Exists (n := Just v)  ::: _) = go (let' (Local n := v) p) ctx
        go p (ctx :> ForAll n              ::: _) = go (lam (Local n) p) ctx


data a := b = a := b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 1 :=

instance Bifoldable (:=) where
  bifoldMap f g (a := b) = f a <> g b

instance Bifunctor (:=) where
  bimap f g (a := b) = f a := g b

instance Bitraversable (:=) where
  bitraverse f g (a := b) = (:=) <$> f a <*> g b

instance (Pretty a, Pretty b) => Pretty (a := b) where
  pretty (a := b) = pretty a <+> magenta (pretty "=") <+> pretty b


data Binding
  = Define (Qualified := Problem (Name Gensym))
  | Exists (Gensym := Maybe (Problem (Name Gensym)))
  | ForAll Gensym
  deriving (Eq, Ord, Show)

bindingName :: Binding -> Name Gensym
bindingName (Define (n := _)) = Global n
bindingName (Exists (n := _)) = Local n
bindingName (ForAll  n)       = Local n

bindingValue :: Binding -> Maybe (Problem (Name Gensym))
bindingValue (Define (_ := v)) = Just v
bindingValue (Exists (_ := v)) = v
bindingValue (ForAll  _)       = Nothing

lookupBinding :: Name Gensym -> Context -> Maybe (Binding ::: Problem (Name Gensym))
lookupBinding n = Stack.find ((== n) . bindingName . typedTerm)


identity, identityT, constant, constantT, constantTQ :: Problem String

identity = lam "A" (lam "a" (pure "a"))
identityT = pi ("A" ::: type') (pi ("_" ::: pure "A") (pure "A"))
constant = lam "A" (lam "B" (lam "a" (lam "b" (pure "a"))))
constantT = pi ("A" ::: type') (pi ("B" ::: type') (pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))

constantTQ
  = exists ("_A" ::: type') (pi ("A" ::: pure "_A")
  ( exists ("_B" ::: type') (pi ("B" ::: pure "_B")
  ( pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))))
