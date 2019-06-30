{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}
module Path.Problem where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Monad (ap)
import           Data.Foldable (fold)
import           Data.List (intersperse)
import qualified Data.Set as Set
import qualified Path.Core as Core
import           Path.Error
import           Path.Module
import           Path.Name
import           Path.Plicity (Plicit (..))
import           Path.Pretty
import           Path.Stack as Stack
import           Path.Usage
import           Prelude hiding (pi)
import           Text.Trifecta.Rendering (Span (..), Spanned (..))

-- FIXME: represent errors explicitly in the tree
-- FIXME: represent spans explicitly in the tree
data Problem a
  = Var a
  | Lam (Problem a) (Problem (Incr (Problem a)))
  | Problem a :$ Problem a
  | Type
  | Pi (Problem a) (Problem (Incr (Problem a)))
  | Ex (Maybe (Problem a)) (Problem a) (Problem (Incr (Problem a)))
  | Problem a :===: Problem a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 3 :===:

instance Applicative Problem where
  pure = Var
  (<*>) = ap

instance Monad Problem where
  a >>= f = efold Ex (:===:) id Type Lam Pi (:$) pure f a

instance Pretty (Problem (Name Gensym)) where
  pretty = prettyPrec 0 . run . runNaming (Root "pretty") . go
    where go = \case
            Ex Nothing t b -> do
              n <- Local <$> gensym "ex"
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (magenta (pretty "∃") <+> pretty (n ::: t') <+> magenta dot </> b'))
            Ex (Just v) t b -> do
              n <- Local <$> gensym "let"
              t' <- prettyPrec 1 <$> go t
              v' <- prettyPrec 0 <$> go v
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (magenta (pretty "let") <+> pretty ((n ::: t') := v') <+> magenta dot </> b'))
            p1 :===: p2 -> do
              p1' <- prettyPrec 1 <$> go p1
              p2' <- prettyPrec 1 <$> go p2
              pure (prec 0 (flatAlt (p1' <+> eq <+> p2') (align (space <+> p1' </> eq <+> p2'))))
            Var (Global (_ :.: n)) -> pure (atom (pretty n))
            Var (Local n) -> pure (atom (pretty '_' <> pretty n)) -- FIXME: distinguish local & meta variables using the context
            Type -> pure (atom (yellow (pretty "Type")))
            Lam t b -> do
              n <- Local <$> gensym "lam"
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (pretty (cyan backslash) <+> pretty (n ::: t') <+> cyan dot </> b'))
            Pi t b -> do
              n <- Local <$> gensym "pi"
              let b' = instantiate (pure n) b
              t' <- prettyPrec 1 <$> go t
              b'' <- prettyPrec 0 <$> go b'
              if n `Set.member` fvs b' then do
                pure (prec 0 (parens (pretty (n ::: t')) <+> arrow <+> b''))
              else do
                pure (prec 0 (pretty t' <+> arrow <+> b''))
            f :$ a -> do
              f' <- prettyPrec 10 <$> go f
              a' <- prettyPrec 11 <$> go a
              pure (prec 10 (f' <+> a'))
          arrow = blue (pretty "->")
          eq = magenta (pretty "≡")

instance Ord a => FreeVariables a (Problem a) where
  fvs = foldMap Set.singleton

exists :: Eq a => a := Maybe (Problem a) ::: Problem a -> Problem a -> Problem a
exists (n := Just v ::: _) (Var n') | n == n' = v
exists (n := v ::: t)      b                  = Ex v t (bind n b)

unexists :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unexists n (Ex Nothing t b) = pure (n ::: t, instantiate (pure n) b)
unexists _ _                = empty

let' :: Eq a => a := Problem a ::: Problem a -> Problem a -> Problem a
let' (n := v ::: t) b = Ex (Just v) t (bind n b)

unlet' :: Alternative m => a -> Problem a -> m (a := Problem a ::: Problem a, Problem a)
unlet' n (Ex (Just v) t b) = pure (n := v ::: t, instantiate (pure n) b)
unlet' _ _                 = empty

(===) :: Eq a => Problem a -> Problem a -> Problem a
p === q
  | p == q    = p
  | otherwise = p :===: q

infixr 3 ===

(?===?) :: Eq a => Maybe (Problem a) -> Maybe (Problem a) -> Maybe (Problem a)
Nothing ?===? Nothing = Nothing
Just p  ?===? Nothing = Just p
Nothing ?===? Just q  = Just q
Just p  ?===? Just q
  | p == q    = Just p
  | otherwise = Just (p :===: q)

infixr 3 ?===?

lam :: Eq a => a ::: Problem a -> Problem a -> Problem a
lam (n ::: t) b = Lam t (bind n b)

lams :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unlam n (Lam t b) = pure (n ::: t, instantiate (pure n) b)
unlam _ _         = empty

pi :: Eq a => a ::: Problem a -> Problem a -> Problem a
pi (n ::: t) b = Pi t (bind n b)

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unpi n (Pi t b) = pure (n ::: t, instantiate (pure n) b)
unpi _ _        = empty


efold :: forall m n a b
      .  (forall a . Maybe (n a) -> n a -> n (Incr (n a)) -> n a)
      -> (forall a . n a -> n a -> n a)
      -> (forall a . m a -> n a)
      -> (forall a . n a)
      -> (forall a . n a -> n (Incr (n a)) -> n a)
      -> (forall a . n a -> n (Incr (n a)) -> n a)
      -> (forall a . n a -> n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (a -> m b)
      -> Problem a
      -> n b
efold ex u var ty lam pi app k = go
  where go :: forall x y . (x -> m y) -> Problem x -> n y
        go h = \case
          Ex v t b -> ex (go h <$> v) (go h t) (go (k . fmap (go h)) b)
          p1 :===: p2 -> u (go h p1) (go h p2)
          Var a -> var (h a)
          Type -> ty
          Lam t b -> lam (go h t) (go (k . fmap (go h)) b)
          Pi t b -> pi (go h t) (go (k . fmap (go h)) b)
          f :$ a -> app (go h f) (go h a)


type Context = Stack (Binding ::: Problem (Name Gensym))

assume :: ( Carrier sig m
          , Member (Error Doc) sig
          , Member (Reader Span) sig
          , Member (State Context) sig
          )
       => Name Gensym
       -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
assume v = do
  _A <- have v
  pure (Var v ::: _A)

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (State Context) sig
         )
      => (Gensym -> m (Problem (Name Gensym) ::: Problem (Name Gensym)))
      -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
intro body = do
  _A <- meta Type
  x <- gensym "intro"
  _B <- ForAll x ::: _A |- meta Type
  u <- ForAll x ::: _A |- goalIs _B (body x)
  pure (lam (Local x ::: _A) u ::: pi (Local x ::: _A) _B)

(-->) :: ( Carrier sig m
         , Member Naming sig
         , Member (State Context) sig
         )
      => m (Problem (Name Gensym) ::: Problem (Name Gensym))
      -> (Gensym -> m (Problem (Name Gensym) ::: Problem (Name Gensym)))
      -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
t --> body = do
  t' <- goalIs Type t
  x <- gensym "pi"
  b' <- ForAll x ::: t' |- goalIs Type (body x)
  pure (pi (Local x ::: t') b' ::: Type)

app :: ( Carrier sig m
       , Member Naming sig
       , Member (State Context) sig
       )
    => m (Problem (Name Gensym) ::: Problem (Name Gensym))
    -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
    -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
app f a = do
  _A <- meta Type
  x <- gensym "app"
  _B <- ForAll x ::: _A |- meta Type
  let _F = pi (Local x ::: _A) _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' :$ a' ::: _F :$ a')


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
  n <- gensym "meta"
  pure (exists (Local n := Nothing ::: ty) (pure (Local n)))

(|-) :: (Carrier sig m, Member (State Context) sig) => Binding ::: Problem (Name Gensym) -> m a -> m a
b |- m = do
  stack <- get
  put (stack :> b)
  a <- m
  a <$ put stack

infix 3 |-

bindMeta :: (Carrier sig m, Member (State Context) sig) => Gensym ::: Problem (Name Gensym) -> m a -> m (Binding, a)
bindMeta (e ::: t) m = Exists (e := Nothing) ::: t |- do
  a <- m
  stack <- get @Context
  case stack of
    Nil           -> pure (Exists (e := Nothing), a)
    _ :> e' ::: _ -> pure (e', a)

solve :: (Carrier sig m, Member (State Context) sig) => Gensym := Problem (Name Gensym) -> m ()
solve (var := val) = modify (fmap @Stack (\ (b ::: t) -> (if bindingName b == Local var then Exists (var := Just val) else b) ::: (t `asTypeOf` val)))

have :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member (Reader Span) sig
        , Member (State Context) sig
        )
     => Name Gensym
     -> m (Problem (Name Gensym))
have n = lookup n >>= maybe (freeVariable n) pure
  where lookup n = fmap typedType <$> lookupBinding n


spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)

elab :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member Naming sig
        , Member (Reader Span) sig
        , Member (State Context) sig
        )
     => Core.Core (Name Gensym)
     -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
elab = \case
  Core.Var n -> assume n
  Core.Lam _ b -> intro (\ n' -> elab (instantiate (pure (Local n')) b))
  f Core.:$ (_ :< a) -> app (elab f) (elab a)
  Core.Type -> pure (Type ::: Type)
  Core.Pi (_ :< _ ::: _ :@ t) b -> elab t --> \ n' -> elab (instantiate (pure (Local n')) b)
  Core.Hole h -> (pure (Local h) :::) <$> meta Type
  Core.Ann ann b -> spanIs ann (elab b)

elabDecl :: ( Carrier sig m
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (State Context) sig
            )
         => Spanned (Decl Qualified (Core.Core (Name Gensym) ::: Core.Core (Name Gensym)))
         -> m (Spanned (Decl Qualified (Problem (Name Gensym) ::: Problem (Name Gensym))))
elabDecl (Decl d name (tm ::: ty) :~ span) = namespace (show name) . runReader span . fmap (:~ span) $ do
  ctx <- get
  ty' <- runReader ctx (declare    (elab ty))
  def <- meta ty'
  tm' <- runReader (ctx :> Define (name := def) ::: ty') (define ty' (elab tm))
  put (ctx :> Define (name := tm') ::: ty')
  pure (Decl d name (tm' ::: ty'))

declare :: ( Carrier sig m
           , Member (Error Doc) sig
           , Member Naming sig
           , Member (Reader Span) sig
           , Member (State Context) sig
           )
        => m (Problem (Name Gensym) ::: Problem (Name Gensym))
        -> m (Problem (Name Gensym))
declare ty = goalIs Type ty >>= simplify

define :: ( Carrier sig m
          , Member (Error Doc) sig
          , Member Naming sig
          , Member (Reader Span) sig
          , Member (State Context) sig
          )
       => Problem (Name Gensym)
       -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
       -> m (Problem (Name Gensym))
define ty tm = goalIs ty tm >>= simplify


simplify :: ( Carrier sig m
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (Reader Span) sig
            , Member (State Context) sig
            )
         => Problem (Name Gensym)
         -> m (Problem (Name Gensym))
simplify = \case
  Ex Nothing t b -> do
    n <- gensym "ex"
    t' <- simplify t
    (v', b') <- (n ::: t') `bindMeta` simplify (instantiate (pure (Local n)) b)
    pure (exists (Local n := bindingValue v' ::: t') b')
  Ex (Just v) t b -> do
    n <- gensym "let"
    v' <- simplify v
    t' <- simplify t
    b' <- Exists (n := Just v') ::: t' |- simplify (instantiate (pure (Local n)) b)
    pure (let' (Local n := v' ::: t') b')
  t1 :===: t2 -> do
    q <- (,) <$> simplify t1 <*> simplify t2
    case q of
      (t1, t2) | t1 == t2 -> pure t1
      (Ex v1 t1 b1, Ex v2 t2 b2) -> do
        n <- gensym "ex"
        t' <- simplify (t1 === t2)
        v' <- maybe (pure Nothing) (fmap Just . simplify) (v1 ?===? v2)
        (v'', b') <- (n ::: t') `bindMeta` simplify (instantiate (pure (Local n)) b1 === instantiate (pure (Local n)) b2)
        pure (exists (Local n := (v' <|> bindingValue v'') ::: t') b')
      (Ex v1 t1 b1, tm2) -> do
        n <- gensym "ex"
        t1' <- simplify t1
        v' <- maybe (pure Nothing) (fmap Just . simplify) v1
        (v'', tm1') <- (n ::: t1') `bindMeta` simplify (instantiate (pure (Local n)) b1 === tm2)
        pure (exists (Local n := (v' <|> bindingValue v'') ::: t1') tm1')
      (tm1, Ex v2 t2 b2) -> do
        n <- gensym "ex"
        t2' <- simplify t2
        v' <- maybe (pure Nothing) (fmap Just . simplify) v2
        (v'', tm2') <- (n ::: t2') `bindMeta` simplify (tm1 === instantiate (pure (Local n)) b2)
        pure (exists (Local n := (v' <|> bindingValue v'') ::: t2') tm2')
      (Var (Local v1), t2) -> simplifyVar v1 t2
      (t1, Var (Local v2)) -> simplifyVar v2 t1
      (Pi t1 b1, Pi t2 b2) -> do
        n <- gensym "pi"
        t' <- simplify (t1 === t2)
        ForAll n ::: t' |- pi (Local n ::: t') <$> simplify (instantiate (pure (Local n)) b1 === instantiate (pure (Local n)) b2)
      (Lam t1 b1, Lam t2 b2) -> do
        n <- gensym "lam"
        t' <- simplify (t1 === t2)
        ForAll n ::: t' |- lam (Local n ::: t') <$> simplify (instantiate (pure (Local n)) b1 === instantiate (pure (Local n)) b2)
      (t1, t2) -> pure (t1 :===: t2)
  Var a -> pure (Var a)
  Type -> pure Type
  Lam t b -> do
    n <- gensym "lam"
    t' <- simplify t
    b' <- ForAll n ::: t' |- simplify (instantiate (pure (Local n)) b)
    pure (lam (Local n ::: t') b')
  Pi t b -> do
    n <- gensym "pi"
    t' <- simplify t
    b' <- ForAll n ::: t' |- simplify (instantiate (pure (Local n)) b)
    pure (pi (Local n ::: t') b')
  f :$ a -> do
    f' <- simplify f
    a' <- simplify a
    pure (f' :$ a')

simplifyVar :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Member (State Context) sig) => Gensym -> Problem (Name Gensym) -> m (Problem (Name Gensym))
simplifyVar v t = do
  v' <- lookupBinding (Local v)
  case v' of
    -- FIXME: occurs check
    Just (Exists (n := _) ::: _) -> pure (Local v) <$ solve (n := t)
    Just _ -> do
      p <- contextualize (pure (Local v) :===: t)
      ask >>= unsimplifiable . pure . (p :~)
    Nothing -> freeVariable v

contextualize :: (Carrier sig m, Member (State Context) sig) => Problem (Name Gensym) -> m (Problem (Name Gensym))
contextualize = gets . go
  where go p Nil                            = p
        go p (ctx :> Define _        ::: _) = go p ctx
        go p (ctx :> Exists (n := v) ::: t) = go (exists (Local n := v ::: t) p) ctx
        go p (ctx :> ForAll n        ::: t) = go (lam (Local n ::: t) p) ctx


unsimplifiable :: (Carrier sig m, Member (Error Doc) sig, Pretty a) => [Spanned a] -> m a
unsimplifiable constraints = throwError (fold (intersperse hardline (map format constraints)))
  where format (c :~ span) = prettyErr span (pretty "unsimplifiable constraint") [pretty c]


data a := b = a := b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 1 :=

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

lookupBinding :: (Carrier sig m, Member (State Context) sig) => Name Gensym -> m (Maybe (Binding ::: Problem (Name Gensym)))
lookupBinding n = gets (Stack.find ((== n) . bindingName . typedTerm))


runProblem :: Functor m => ReaderC Span (StateC Context m) a -> m a
runProblem = evalState (mempty :: Context) . runReader (Span mempty mempty mempty)
