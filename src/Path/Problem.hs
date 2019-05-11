{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}
module Path.Problem where

import Control.Applicative (Alternative(..))
import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Control.Monad (ap)
import Data.Foldable (fold)
import Data.List (intersperse)
import Path.Constraint (Equation(..))
import qualified Path.Core as Core
import Path.Error
import Path.Module
import Path.Name
import Path.Plicity (Plicit(..))
import Path.Pretty
import Path.Stack as Stack
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span(..), Spanned(..))

-- FIXME: represent errors explicitly in the tree
-- FIXME: represent spans explicitly in the tree
data Problem a
  = Ex (Maybe (Problem a)) (Problem a) (Problem (Incr a))
  | U (Equation (Problem a))
  | Var (Name a)
  | Type
  | Lam (Problem a) (Problem (Incr a))
  | Pi (Problem a) (Problem a)
  | Problem a :$ Problem a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Problem where
  pure = Var . Local
  (<*>) = ap

instance Monad Problem where
  a >>= f = joinT (f <$> a)

instance Pretty (Problem Meta) where
  pretty = prettyPrec 0 . run . runNaming (Root "pretty") . go
    where go = \case
            Ex Nothing t b -> do
              n <- Meta <$> gensym "ex"
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (magenta (pretty "∃") <+> pretty (n ::: t') <+> magenta dot </> b'))
            Ex (Just v) t b -> do
              n <- Meta <$> gensym "let"
              t' <- prettyPrec 1 <$> go t
              v' <- prettyPrec 0 <$> go v
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (magenta (pretty "let") <+> pretty ((n ::: t') := v') <+> magenta dot </> b'))
            U q -> do
              q' <- traverse go q
              pure (prec 0 (pretty (prettyPrec 1 <$> q')))
            Var (Global (_ :.: n)) -> pure (atom (pretty n))
            Var (Local (Name n)) -> pure (atom (pretty '_' <> pretty n))
            Var (Local n) -> pure (atom (pretty n))
            Type -> pure (atom (yellow (pretty "Type")))
            Lam t b -> do
              n <- Name <$> gensym "lam"
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (pretty (cyan backslash) <+> pretty (n ::: t') <+> cyan dot </> b'))
            Pi t (Lam _ b) -> do
              n <- Name <$> gensym "pi"
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (parens (pretty (n ::: t')) <+> arrow <+> b'))
            Pi t b -> do
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go b
              pure (prec 0 (pretty t' <+> arrow <+> b'))
            f :$ a -> do
              f' <- prettyPrec 10 <$> go f
              a' <- prettyPrec 11 <$> go a
              pure (prec 10 (f' <+> a'))
          arrow = blue (pretty "->")

exists :: Eq a => a ::: Problem a -> Problem a -> Problem a
exists (n ::: t) b = Ex Nothing t (bind n b)

unexists :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unexists n (Ex Nothing t b) = pure (n ::: t, instantiate (pure n) b)
unexists _ _        = empty

let' :: Eq a => a := Problem a ::: Problem a -> Problem a -> Problem a
let' (n := v ::: t) b = Ex (Just v) t (bind n b)

unlet' :: Alternative m => a -> Problem a -> m (a := Problem a ::: Problem a, Problem a)
unlet' n (Ex (Just v) t b) = pure (n := v ::: t, instantiate (pure n) b)
unlet' _ _                 = empty

(===) :: Problem a -> Problem a -> Problem a
p === q = U (p :===: q)

infixr 3 ===

lam :: Eq a => a ::: Problem a -> Problem a -> Problem a
lam (n ::: t) b = Lam t (bind n b)

lams :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unlam n (Lam t b) = pure (n ::: t, instantiate (pure n) b)
unlam _ _         = empty

pi :: Eq a => a ::: Problem a -> Problem a -> Problem a
pi (n ::: t) b = Pi t (Lam t (bind n b))

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unpi n (Pi t (Lam _ b)) = pure (n ::: t, instantiate (pure n) b)
unpi _ _                = empty


gfoldT :: forall m n b
       .  (forall a . Maybe (n a) -> n a -> n (Incr a) -> n a)
       -> (forall a . Equation (n a) -> n a)
       -> (forall a . Name (m a) -> n a)
       -> (forall a . n a)
       -> (forall a . n a -> n (Incr a) -> n a)
       -> (forall a . n a -> n a -> n a)
       -> (forall a . n a -> n a -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Problem (m b)
       -> n b
gfoldT ex u var ty lam pi app dist = go
  where go :: Problem (m x) -> n x
        go = \case
          Ex v t b -> ex (go <$> v) (go t) (go (dist <$> b))
          U (a :===: b) -> u (go a :===: go b)
          Var a -> var a
          Type -> ty
          Lam t b -> lam (go t) (go (dist <$> b))
          Pi t b -> pi (go t) (go b)
          f :$ a -> go f `app` go a

joinT :: Problem (Problem a) -> Problem a
joinT = gfoldT Ex U (name id (Var . Global)) Type Lam Pi (:$) (incr (pure Z) (fmap S))


-- | Bind occurrences of a name in a 'Value' term, producing a 'Problem' in which the name is bound.
bind :: Eq a => a -> Problem a -> Problem (Incr a)
bind name = fmap (match name)

-- | Substitute a 'Problem' term for the free variable in a given 'Problem', producing a closed 'Problem' term.
instantiate :: Problem a -> Problem (Incr a) -> Problem a
instantiate t b = b >>= subst t . fmap pure


type Context = Stack (Binding ::: Problem Meta)

assume :: ( Carrier sig m
          , Member (Error Doc) sig
          , Member (Reader Span) sig
          , Member (State Context) sig
          )
       => Name Gensym
       -> m (Problem Meta ::: Problem Meta)
assume v = do
  _A <- have v
  pure (Var (Name <$> v) ::: _A)

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (State Context) sig
         )
      => (Gensym -> m (Problem Meta ::: Problem Meta))
      -> m (Problem Meta ::: Problem Meta)
intro body = do
  _A <- meta Type
  x <- gensym "intro"
  _B <- ForAll x ::: _A |- meta Type
  u <- ForAll x ::: _A |- goalIs _B (body x)
  pure (lam (Name x ::: _A) u ::: pi (Name x ::: _A) _B)

(-->) :: ( Carrier sig m
         , Member Naming sig
         , Member (State Context) sig
         )
      => m (Problem Meta ::: Problem Meta)
      -> (Gensym -> m (Problem Meta ::: Problem Meta))
      -> m (Problem Meta ::: Problem Meta)
t --> body = do
  t' <- goalIs Type t
  x <- gensym "pi"
  b' <- ForAll x ::: t' |- goalIs Type (body x)
  pure (pi (Name x ::: t') b' ::: Type)

app :: ( Carrier sig m
       , Member Naming sig
       , Member (State Context) sig
       )
    => m (Problem Meta ::: Problem Meta)
    -> m (Problem Meta ::: Problem Meta)
    -> m (Problem Meta ::: Problem Meta)
app f a = do
  _A <- meta Type
  x <- gensym "app"
  _B <- ForAll x ::: _A |- meta Type
  let _F = pi (Name x ::: _A) _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' :$ a' ::: _F :$ a')


goalIs :: ( Carrier sig m
          , Member Naming sig
          )
       => Problem Meta
       -> m (Problem Meta ::: Problem Meta)
       -> m (Problem Meta)
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- meta (ty1 === ty2)
  pure (tm1 === tm2)

meta :: (Carrier sig m, Member Naming sig) => Problem Meta -> m (Problem Meta)
meta ty = do
  n <- gensym "meta"
  pure (exists (Meta n ::: ty) (pure (Meta n)))

(|-) :: (Carrier sig m, Member (State Context) sig) => Binding ::: Problem Meta -> m a -> m a
b |- m = do
  stack <- get
  put (stack :> b)
  a <- m
  a <$ put stack

infix 3 |-

bindMeta :: (Carrier sig m, Member (State Context) sig) => Gensym ::: Problem Meta -> m a -> m (Binding, a)
bindMeta (e ::: t) m = Exists (e := Nothing) ::: t |- do
  a <- m
  stack <- get @Context
  case stack of
    Nil -> pure (Exists (e := Nothing), a)
    _ :> e' ::: _ -> pure (e', a)

solve :: (Carrier sig m, Member (State Context) sig) => Gensym := Problem Meta -> m ()
solve (var := val) = modify (fmap @Stack (\ (b ::: t) -> (if bindingName b == Local (Meta var) then Exists (var := Just val) else b) ::: (t `asTypeOf` val)))

have :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member (Reader Span) sig
        , Member (State Context) sig
        )
     => Name Gensym
     -> m (Problem Meta)
have n = lookup (Name <$> n) >>= maybe (freeVariable n) pure
  where lookup n = fmap typedType <$> lookupBinding n


spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)

elab :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member Naming sig
        , Member (Reader Span) sig
        , Member (State Context) sig
        )
     => Core.Core Gensym
     -> m (Problem Meta ::: Problem Meta)
elab = \case
  Core.Var n -> assume n
  Core.Lam _ b -> intro (\ n' -> elab (Core.instantiate (pure n') b))
  f Core.:$ (_ :< a) -> app (elab f) (elab a)
  Core.Type -> pure (Type ::: Type)
  Core.Pi _ t (Core.Lam _ b) -> elab t --> \ n' -> elab (Core.instantiate (pure n') b)
  Core.Pi _ t b -> elab t --> \ _ -> elab b
  Core.Hole h -> (pure (Meta h) :::) <$> meta Type
  Core.Ann ann b -> spanIs ann (elab b)

elabDecl :: ( Carrier sig m
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (State Context) sig
            )
         => Spanned (Decl Qualified (Core.Core Gensym ::: Core.Core Gensym))
         -> m (Spanned (Decl Qualified (Problem Meta ::: Problem Meta)))
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
        => m (Problem Meta ::: Problem Meta)
        -> m (Problem Meta)
declare ty = goalIs Type ty >>= simplify

define :: ( Carrier sig m
          , Member (Error Doc) sig
          , Member Naming sig
          , Member (Reader Span) sig
          , Member (State Context) sig
          )
       => Problem Meta
       -> m (Problem Meta ::: Problem Meta)
       -> m (Problem Meta)
define ty tm = goalIs ty tm >>= simplify


simplify :: ( Carrier sig m
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (Reader Span) sig
            , Member (State Context) sig
            )
         => Problem Meta
         -> m (Problem Meta)
simplify = \case
  Ex Nothing t b -> do
    n <- gensym "ex"
    t' <- simplify t
    (v, b') <- (n ::: t') `bindMeta` simplify (instantiate (pure (Meta n)) b)
    case v of
      Exists (_ := Just v') -> pure (let' (Meta n := v' ::: t') b')
      _ -> pure (exists (Meta n ::: t') b')
  Ex (Just v) t b -> do
    n <- gensym "let"
    v' <- simplify v
    t' <- simplify t
    b' <- Exists (n := Just v') ::: t' |- simplify (instantiate (pure (Meta n)) b)
    pure (let' (Meta n := v' ::: t') b')
  U (t1 :===: t2) -> do
    q <- (:===:) <$> simplify t1 <*> simplify t2
    case q of
      t1 :===: t2 | t1 == t2 -> pure t1
      Ex v1 t1 b1 :===: Ex v2 t2 b2 -> do
        n <- gensym "ex"
        t' <- simplify (t1 === t2)
        (_, b') <- (n ::: t') `bindMeta` simplify (instantiate (pure (Meta n)) b1 === instantiate (pure (Meta n)) b2)
        pure (exists (Meta n ::: t') b')
      Ex v1 t1 b1 :===: tm2 -> do
        n <- gensym "ex"
        t1' <- simplify t1
        (_, tm1') <- (n ::: t1') `bindMeta` (exists (Meta n ::: t1') <$> simplify (instantiate (pure (Meta n)) b1 === tm2))
        pure tm1'
      tm1 :===: Ex v2 t2 b2 -> do
        n <- gensym "ex"
        t2' <- simplify t2
        (_, tm2') <- (n ::: t2') `bindMeta` (exists (Meta n ::: t2') <$> simplify (tm1 === instantiate (pure (Meta n)) b2))
        pure tm2'
      Var (Local (Meta v1)) :===: t2 -> simplifyVar (Meta v1) t2
      t1 :===: Var (Local (Meta v2)) -> simplifyVar (Meta v2) t1
      Pi t1 (Lam _ b1) :===: Pi t2 (Lam _ b2) -> do
        n <- gensym "pi"
        t' <- simplify (t1 === t2)
        ForAll n ::: t' |- pi (Name n ::: t') <$> simplify (instantiate (pure (Name n)) b1 === instantiate (pure (Name n)) b2)
      Pi t1 b1 :===: Pi t2 b2 -> Pi <$> simplify (t1 === t2) <*> simplify (b1 === b2)
      Lam t1 b1 :===: Lam t2 b2 -> do
        n <- gensym "lam"
        t' <- simplify (t1 === t2)
        ForAll n ::: t' |- lam (Name n ::: t') <$> simplify (instantiate (pure (Name n)) b1 === instantiate (pure (Name n)) b2)
      other -> pure (U other)
  Var a -> pure (Var a)
  Type -> pure Type
  Lam t b -> do
    n <- gensym "lam"
    t' <- simplify t
    b' <- ForAll n ::: t' |- simplify (instantiate (pure (Name n)) b)
    pure (lam (Name n ::: t') b')
  Pi t (Lam _ b) -> do
    n <- gensym "pi"
    t' <- simplify t
    b' <- ForAll n ::: t' |- simplify (instantiate (pure (Name n)) b)
    pure (pi (Name n ::: t') b')
  Pi t b -> Pi <$> simplify t <*> simplify b
  f :$ a -> do
    f' <- simplify f
    a' <- simplify a
    pure (f' :$ a')

simplifyVar :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Member (State Context) sig) => Meta -> Problem Meta -> m (Problem Meta)
simplifyVar v t = do
  v' <- lookupBinding (Local v)
  case v' of
    -- FIXME: occurs check
    Just (Exists (n := _) ::: _) -> t <$ solve (n := t)
    Just _ -> do
      p <- contextualize (U (pure v :===: t))
      ask >>= unsimplifiable . pure . (p :~)
    Nothing -> freeVariable v

contextualize :: (Carrier sig m, Member (State Context) sig) => Problem Meta -> m (Problem Meta)
contextualize = gets . go
  where go p Nil = p
        go p (ctx :> Define _              ::: _) = go p ctx
        go p (ctx :> Exists (n := Nothing) ::: t) = go (exists (Meta n ::: t) p) ctx
        go p (ctx :> Exists (n := Just v)  ::: t) = go (let' (Meta n := v ::: t) p) ctx
        go p (ctx :> ForAll n              ::: t) = go (lam (Name n ::: t) p) ctx


unsimplifiable :: (Carrier sig m, Member (Error Doc) sig, Pretty a) => [Spanned a] -> m a
unsimplifiable constraints = throwError (fold (intersperse hardline (map format constraints)))
  where format (c :~ span) = prettyErr span (pretty "unsimplifiable constraint") [pretty c]


data a := b = a := b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 1 :=

instance (Pretty a, Pretty b) => Pretty (a := b) where
  pretty (a := b) = pretty a <+> magenta (pretty "=") <+> pretty b


data Binding
  = Define (Qualified := Problem Meta)
  | Exists (Gensym := Maybe (Problem Meta))
  | ForAll Gensym
  deriving (Eq, Ord, Show)

bindingName :: Binding -> Name Meta
bindingName (Define (n := _)) = Global n
bindingName (Exists (n := _)) = Local (Meta n)
bindingName (ForAll  n)       = Local (Name n)

bindingValue :: Binding -> Maybe (Problem Meta)
bindingValue (Define (_ := v)) = Just v
bindingValue (Exists (_ := v)) = v
bindingValue (ForAll  _)       = Nothing

lookupBinding :: (Carrier sig m, Member (State Context) sig) => Name Meta -> m (Maybe (Binding ::: Problem Meta))
lookupBinding n = gets (Stack.find ((== n) . bindingName . typedTerm))


runProblem :: Functor m => ReaderC Span (StateC Context m) a -> m a
runProblem = evalState (mempty :: Context) . runReader (Span mempty mempty mempty)
