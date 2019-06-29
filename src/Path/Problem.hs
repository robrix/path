{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeOperators #-}
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
data ProblemF f a
  = Ex (Maybe (f a)) (f a) (f (Incr (f a)))
  | U (Equation (f a))
  | Var (Name a)
  | Type
  | Lam (f a) (f (Incr (f a)))
  | Pi (f a) (f a)
  | f a :$ f a
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (ProblemF f a)
deriving instance (Ord  a, forall x . Eq   x => Eq   (f x)
                         , forall x . Ord  x => Ord  (f x)) => Ord  (ProblemF f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (ProblemF f a)

newtype Problem a = Problem { unProblem :: ProblemF Problem a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Problem where
  pure = Problem . Var . Local
  (<*>) = ap

instance Monad Problem where
  a >>= f = gfold ex (Problem . U) (name id (Problem . Var . Global)) (Problem Type) lam pi ($$) pure (f <$> a)
    where ex v t b = Problem (Ex v t b)
          lam t b = Problem (Lam t b)
          pi t b = Problem (Pi t b)
          f $$ a = Problem (f :$ a)

instance Pretty (Problem Meta) where
  pretty = prettyPrec 0 . run . runNaming (Root "pretty") . go
    where go = \case
            Problem (Ex Nothing t b) -> do
              n <- Meta <$> gensym "ex"
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (magenta (pretty "∃") <+> pretty (n ::: t') <+> magenta dot </> b'))
            Problem (Ex (Just v) t b) -> do
              n <- Meta <$> gensym "let"
              t' <- prettyPrec 1 <$> go t
              v' <- prettyPrec 0 <$> go v
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (magenta (pretty "let") <+> pretty ((n ::: t') := v') <+> magenta dot </> b'))
            Problem (U q) -> do
              q' <- traverse go q
              pure (prec 0 (pretty (prettyPrec 1 <$> q')))
            Problem (Var (Global (_ :.: n))) -> pure (atom (pretty n))
            Problem (Var (Local (Name n))) -> pure (atom (pretty '_' <> pretty n))
            Problem (Var (Local n)) -> pure (atom (pretty n))
            Problem Type -> pure (atom (yellow (pretty "Type")))
            Problem (Lam t b) -> do
              n <- Name <$> gensym "lam"
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (pretty (cyan backslash) <+> pretty (Local n ::: t') <+> cyan dot </> b'))
            Problem (Pi t (Problem (Lam _ b))) -> do
              n <- Name <$> gensym "pi"
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go (instantiate (pure n) b)
              pure (prec 0 (parens (pretty (Local n ::: t')) <+> arrow <+> b'))
            Problem (Pi t b) -> do
              t' <- prettyPrec 1 <$> go t
              b' <- prettyPrec 0 <$> go b
              pure (prec 0 (pretty t' <+> arrow <+> b'))
            Problem (f :$ a) -> do
              f' <- prettyPrec 10 <$> go f
              a' <- prettyPrec 11 <$> go a
              pure (prec 10 (f' <+> a'))
          arrow = blue (pretty "->")

exists :: Eq a => a := Maybe (Problem a) ::: Problem a -> Problem a -> Problem a
exists (n := Just v ::: _) (Problem (Var (Local n'))) | n == n' = v
exists (n := v ::: t)      b                                    = Problem (Ex v t (bind n b))

unexists :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unexists n (Problem (Ex Nothing t b)) = pure (n ::: t, instantiate (pure n) b)
unexists _ _                          = empty

let' :: Eq a => a := Problem a ::: Problem a -> Problem a -> Problem a
let' (n := v ::: t) b = Problem (Ex (Just v) t (bind n b))

unlet' :: Alternative m => a -> Problem a -> m (a := Problem a ::: Problem a, Problem a)
unlet' n (Problem (Ex (Just v) t b)) = pure (n := v ::: t, instantiate (pure n) b)
unlet' _ _                           = empty

(===) :: Eq a => Problem a -> Problem a -> Problem a
p === q
  | p == q    = p
  | otherwise = Problem (U (p :===: q))

infixr 3 ===

(?===?) :: Eq a => Maybe (Problem a) -> Maybe (Problem a) -> Maybe (Problem a)
Nothing ?===? Nothing = Nothing
Just p  ?===? Nothing = Just p
Nothing ?===? Just q  = Just q
Just p  ?===? Just q
  | p == q    = Just p
  | otherwise = Just (Problem (U (p :===: q)))

infixr 3 ?===?

lam :: Eq a => a ::: Problem a -> Problem a -> Problem a
lam (n ::: t) b = Problem (Lam t (bind n b))

lams :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unlam n (Problem (Lam t b)) = pure (n ::: t, instantiate (pure n) b)
unlam _ _                   = empty

pi :: Eq a => a ::: Problem a -> Problem a -> Problem a
pi (n ::: t) b = Problem (Pi t (lam (n ::: t) b))

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unpi n (Problem (Pi t (Problem (Lam _ b)))) = pure (n ::: t, instantiate (pure n) b)
unpi _ _                        = empty


gfold :: forall m n b
      .  (forall a . Maybe (n a) -> n a -> n (Incr (n a)) -> n a)
      -> (forall a . Equation (n a) -> n a)
      -> (forall a . Name (m a) -> n a)
      -> (forall a . n a)
      -> (forall a . n a -> n (Incr (n a)) -> n a)
      -> (forall a . n a -> n a -> n a)
      -> (forall a . n a -> n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> Problem (m b)
      -> n b
gfold ex u var ty lam pi app k = go
  where go :: Problem (m x) -> n x
        go = \case
          Problem (Ex v t b) -> ex (go <$> v) (go t) (go (k . fmap go <$> b))
          Problem (U (a :===: b)) -> u (go a :===: go b)
          Problem (Var a) -> var a
          Problem Type -> ty
          Problem (Lam t b) -> lam (go t) (go (k . fmap go <$> b))
          Problem (Pi t b) -> pi (go t) (go b)
          Problem (f :$ a) -> go f `app` go a


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
  pure (Problem (Var (Name <$> v)) ::: _A)

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (State Context) sig
         )
      => (Gensym -> m (Problem Meta ::: Problem Meta))
      -> m (Problem Meta ::: Problem Meta)
intro body = do
  _A <- meta (Problem Type)
  x <- gensym "intro"
  _B <- ForAll x ::: _A |- meta (Problem Type)
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
  t' <- goalIs (Problem Type) t
  x <- gensym "pi"
  b' <- ForAll x ::: t' |- goalIs (Problem Type) (body x)
  pure (pi (Name x ::: t') b' ::: Problem Type)

app :: ( Carrier sig m
       , Member Naming sig
       , Member (State Context) sig
       )
    => m (Problem Meta ::: Problem Meta)
    -> m (Problem Meta ::: Problem Meta)
    -> m (Problem Meta ::: Problem Meta)
app f a = do
  _A <- meta (Problem Type)
  x <- gensym "app"
  _B <- ForAll x ::: _A |- meta (Problem Type)
  let _F = pi (Name x ::: _A) _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (Problem (f' :$ a') ::: Problem (_F :$ a'))


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
  pure (exists (Meta n := Nothing ::: ty) (pure (Meta n)))

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
  Core.Lam _ b -> intro (\ n' -> elab (instantiate (pure n') b))
  f Core.:$ (_ :< a) -> app (elab f) (elab a)
  Core.Type -> pure (Problem Type ::: Problem Type)
  Core.Pi _ t (Core.Lam _ b) -> elab t --> \ n' -> elab (instantiate (pure n') b)
  Core.Pi _ t b -> elab t --> \ _ -> elab b
  Core.Hole h -> (pure (Meta h) :::) <$> meta (Problem Type)
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
declare ty = goalIs (Problem Type) ty >>= simplify

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
  Problem (Ex Nothing t b) -> do
    n <- gensym "ex"
    t' <- simplify t
    (v', b') <- (n ::: t') `bindMeta` simplify (instantiate (pure (Meta n)) b)
    pure (exists (Meta n := bindingValue v' ::: t') b')
  Problem (Ex (Just v) t b) -> do
    n <- gensym "let"
    v' <- simplify v
    t' <- simplify t
    b' <- Exists (n := Just v') ::: t' |- simplify (instantiate (pure (Meta n)) b)
    pure (let' (Meta n := v' ::: t') b')
  Problem (U (t1 :===: t2)) -> do
    q <- (:===:) <$> simplify t1 <*> simplify t2
    case q of
      t1 :===: t2 | t1 == t2 -> pure t1
      Problem (Ex v1 t1 b1) :===: Problem (Ex v2 t2 b2) -> do
        n <- gensym "ex"
        t' <- simplify (t1 === t2)
        v' <- maybe (pure Nothing) (fmap Just . simplify) (v1 ?===? v2)
        (v'', b') <- (n ::: t') `bindMeta` simplify (instantiate (pure (Meta n)) b1 === instantiate (pure (Meta n)) b2)
        pure (exists (Meta n := (v' <|> bindingValue v'') ::: t') b')
      Problem (Ex v1 t1 b1) :===: tm2 -> do
        n <- gensym "ex"
        t1' <- simplify t1
        v' <- maybe (pure Nothing) (fmap Just . simplify) v1
        (v'', tm1') <- (n ::: t1') `bindMeta` simplify (instantiate (pure (Meta n)) b1 === tm2)
        pure (exists (Meta n := (v' <|> bindingValue v'') ::: t1') tm1')
      tm1 :===: Problem (Ex v2 t2 b2) -> do
        n <- gensym "ex"
        t2' <- simplify t2
        v' <- maybe (pure Nothing) (fmap Just . simplify) v2
        (v'', tm2') <- (n ::: t2') `bindMeta` simplify (tm1 === instantiate (pure (Meta n)) b2)
        pure (exists (Meta n := (v' <|> bindingValue v'') ::: t2') tm2')
      Problem (Var (Local (Meta v1))) :===: t2 -> simplifyVar (Meta v1) t2
      t1 :===: Problem (Var (Local (Meta v2))) -> simplifyVar (Meta v2) t1
      Problem (Pi t1 (Problem (Lam _ b1))) :===: Problem (Pi t2 (Problem (Lam _ b2))) -> do
        n <- gensym "pi"
        t' <- simplify (t1 === t2)
        ForAll n ::: t' |- pi (Name n ::: t') <$> simplify (instantiate (pure (Name n)) b1 === instantiate (pure (Name n)) b2)
      Problem (Pi t1 b1) :===: Problem (Pi t2 b2) -> Problem <$> (Pi <$> simplify (t1 === t2) <*> simplify (b1 === b2))
      Problem (Lam t1 b1) :===: Problem (Lam t2 b2) -> do
        n <- gensym "lam"
        t' <- simplify (t1 === t2)
        ForAll n ::: t' |- lam (Name n ::: t') <$> simplify (instantiate (pure (Name n)) b1 === instantiate (pure (Name n)) b2)
      other -> pure (Problem (U other))
  Problem (Var a) -> pure (Problem (Var a))
  Problem Type -> pure (Problem Type)
  Problem (Lam t b) -> do
    n <- gensym "lam"
    t' <- simplify t
    b' <- ForAll n ::: t' |- simplify (instantiate (pure (Name n)) b)
    pure (lam (Name n ::: t') b')
  Problem (Pi t (Problem (Lam _ b))) -> do
    n <- gensym "pi"
    t' <- simplify t
    b' <- ForAll n ::: t' |- simplify (instantiate (pure (Name n)) b)
    pure (pi (Name n ::: t') b')
  Problem (Pi t b) -> Problem <$> (Pi <$> simplify t <*> simplify b)
  Problem (f :$ a) -> do
    f' <- simplify f
    a' <- simplify a
    pure (Problem (f' :$ a'))

simplifyVar :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Member (State Context) sig) => Meta -> Problem Meta -> m (Problem Meta)
simplifyVar v t = do
  v' <- lookupBinding (Local v)
  case v' of
    -- FIXME: occurs check
    Just (Exists (n := _) ::: _) -> pure v <$ solve (n := t)
    Just _ -> do
      p <- contextualize (Problem (U (pure v :===: t)))
      ask >>= unsimplifiable . pure . (p :~)
    Nothing -> freeVariable v

contextualize :: (Carrier sig m, Member (State Context) sig) => Problem Meta -> m (Problem Meta)
contextualize = gets . go
  where go p Nil = p
        go p (ctx :> Define _        ::: _) = go p ctx
        go p (ctx :> Exists (n := v) ::: t) = go (exists (Meta n := v ::: t) p) ctx
        go p (ctx :> ForAll n        ::: t) = go (lam (Name n ::: t) p) ctx


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
