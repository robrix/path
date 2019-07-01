{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeOperators #-}
module Path.Problem where

import           Control.Applicative (Alternative (..), Const (..))
import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Writer
import           Data.Coerce
import           Data.Foldable (fold)
import           Data.List (intersperse)
import qualified Data.Set as Set
import           Path.Error
import           Path.Module
import           Path.Name
import           Path.Plicity (Plicit (..))
import           Path.Pretty
import           Path.Stack as Stack
import qualified Path.Surface as Surface
import           Path.Usage
import           Prelude hiding (pi)
import           Text.Trifecta.Rendering (Span (..), Spanned (..))

data Problem a
  = Var a
  | Problem (ProblemF Problem a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Problem where
  pure = Var
  f <*> a = eiter id Problem Var (<$> a) f

instance Monad Problem where
  a >>= f = eiter id Problem Var f a

instance Pretty (Problem (Name Gensym)) where
  pretty = snd . run . runWriter @(Set.Set Meta) . runReader ([] @Meta) . runReader (0 :: Int) . kcata id alg k (var . fmap Name)
    where var (Global v) = pure (pretty (Global @Meta v))
          var (Local  v) = pretty v <$ tell (Set.singleton @Meta v)
          alg = \case
            Lam t (Scope b) -> do
              t' <- withPrec 1 t
              (n, b') <- bind Name (withPrec 0 b)
              prec 0 (pretty (cyan backslash) <+> pretty (n ::: t') </> cyan dot <+> b')
            f :$ a -> do
              f' <- withPrec 10 f
              a' <- withPrec 11 a
              prec 10 (f' <+> a')
            Type -> pure (yellow (pretty "Type"))
            Pi t (Scope b) -> do
              t' <- withPrec 1 t
              (fvs, (n, b')) <- listen (bind Name (withPrec 0 b))
              let t'' | n `Set.member` fvs = parens (pretty (n ::: t'))
                      | otherwise          = t'
              prec 0 (t'' </> arrow <+> b')
            Ex Nothing t (Scope b) -> do
              t' <- withPrec 1 t
              (n, b') <- bind Meta (withPrec 0 b)
              prec 0 (magenta (pretty "∃") <+> pretty (n ::: t') </> magenta dot <+> b')
            Ex (Just v) t (Scope b) -> do
              t' <- withPrec 1 t
              v' <- withPrec 0 v
              (n, b') <- bind Meta (withPrec 0 b)
              prec 0 (magenta (pretty "let") <+> pretty ((n ::: t') := v') </> magenta dot <+> b')
            p1 :===: p2 -> do
              p1' <- withPrec 1 p1
              p2' <- withPrec 1 p2
              prec 0 (flatAlt (p1' <+> eq' <+> p2') (align (space <+> p1' </> eq' <+> p2')))
          arrow = blue (pretty "→")
          eq' = magenta (pretty "≡")
          k Z     = ask >>= var . Local . head
          k (S n) = local (tail @Meta) n
          prec d' doc = do
            d <- ask @Int
            pure (prettyParens (d > d') doc)
          withPrec i = local @Int (const i) . getConst
          bind cons m = do
            ns <- ask
            let n = cons $ case ns of
                  Meta (p :/ (_, i)) :_ -> p :/ ("", succ i)
                  Name (p :/ (_, i)) :_ -> p :/ ("", succ i)
                  _ -> Root :/ ("", 0)
            (,) n <$> censor (Set.delete n) (local (n :) m)

instance Ord a => FreeVariables a (Problem a) where
  fvs = foldMap Set.singleton


-- FIXME: represent errors explicitly in the tree
-- FIXME: represent spans explicitly in the tree
data ProblemF f a
  = Lam (f a) (Scope f a)
  | f a :$ f a
  | Type
  | Pi (f a) (Scope f a)
  | Ex (Maybe (f a)) (f a) (Scope f a)
  | f a :===: f a
  deriving (Foldable, Functor, Traversable)

infix 3 :===:

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (ProblemF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (ProblemF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (ProblemF f a)


lam :: Eq a => a ::: Problem a -> Problem a -> Problem a
lam (n ::: t) b = Problem (Lam t (bind n b))

lams :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unlam n (Problem (Lam t b)) = pure (n ::: t, instantiate (pure n) b)
unlam _ _                   = empty

($$) :: Problem a -> Problem a -> Problem a
f $$ a = Problem (f :$ a)


type' :: Problem a
type' = Problem Type

pi :: Eq a => a ::: Problem a -> Problem a -> Problem a
pi (n ::: t) b = Problem (Pi t (bind n b))

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unpi n (Problem (Pi t b)) = pure (n ::: t, instantiate (pure n) b)
unpi _ _                  = empty


exists :: Eq a => a := Maybe (Problem a) ::: Problem a -> Problem a -> Problem a
exists (n := Just v ::: _) (Var n') | n == n' = v
exists (n := v      ::: t) b                  = Problem (Ex v t (bind n b))

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
  | otherwise = Problem (p :===: q)

infixr 3 ===

(?===?) :: Eq a => Maybe (Problem a) -> Maybe (Problem a) -> Maybe (Problem a)
Nothing ?===? Nothing = Nothing
Just p  ?===? Nothing = Just p
Nothing ?===? Just q  = Just q
Just p  ?===? Just q
  | p == q    = Just p
  | otherwise = Just (Problem (p :===: q))

infixr 3 ?===?


eiter :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . ProblemF n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (a -> m b)
      -> Problem a
      -> n b
eiter var alg k = go
  where go :: forall x y . (x -> m y) -> Problem x -> n y
        go h = \case
          Var a -> var (h a)
          Problem p -> case p of
            Lam t b -> alg (Lam (go h t) (foldScope k go h b))
            f :$ a -> alg (go h f :$ go h a)
            Type -> alg Type
            Pi t b -> alg (Pi (go h t) (foldScope k go h b))
            Ex v t b -> alg (Ex (go h <$> v) (go h t) (foldScope k go h b))
            p1 :===: p2 -> alg (go h p1 :===: go h p2)

kcata :: (a -> b)
      -> (forall a . ProblemF (Const b) a -> b)
      -> (Incr b -> a)
      -> (x -> a)
      -> Problem x
      -> b
kcata var alg k h = getConst . eiter (coerce var) (coerce alg) (coerce k) (Const . h)


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
  _A <- meta type'
  x <- gensym "intro"
  _B <- ForAll x ::: _A |- meta type'
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
  t' <- goalIs type' t
  x <- gensym "pi"
  b' <- ForAll x ::: t' |- goalIs type' (body x)
  pure (pi (Local x ::: t') b' ::: type')

app :: ( Carrier sig m
       , Member Naming sig
       , Member (State Context) sig
       )
    => m (Problem (Name Gensym) ::: Problem (Name Gensym))
    -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
    -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
app f a = do
  _A <- meta type'
  x <- gensym "app"
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
have n = lookupBinding n >>= maybe (freeVariable n) (pure . typedType)


spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)

elab :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member Naming sig
        , Member (Reader Span) sig
        , Member (State Context) sig
        )
     => Surface.Surface (Name Meta)
     -> m (Problem (Name Gensym) ::: Problem (Name Gensym))
elab = \case
  Surface.Var (Global n) -> assume (Global n)
  Surface.Var (Local (Name n)) -> assume (Local n)
  Surface.Var (Local (Meta n)) -> (pure (Local n) :::) <$> meta type'
  Surface.Surface c -> case c of
    Surface.Lam _ b -> intro (\ n' -> elab' (instantiate (pure (Local (Name n'))) <$> b))
    f Surface.:$ (_ :< a) -> app (elab' f) (elab' a)
    Surface.Type -> pure (type' ::: type')
    Surface.Pi (_ :< _ ::: _ :@ t) b -> elab' t --> \ n' -> elab' (instantiate (pure (Local (Name n'))) <$> b)
  where elab' (t :~ s) = spanIs s (elab t)

elabDecl :: ( Carrier sig m
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (State Context) sig
            )
         => Spanned (Decl Qualified (Surface.Surface (Name Meta) ::: Surface.Surface (Name Meta)))
         -> m (Spanned (Decl Qualified (Problem (Name Gensym) ::: Problem (Name Gensym))))
elabDecl (Decl d name (tm ::: ty) :~ span) = namespace (show name) . runReader span . fmap (:~ span) $ do
  ctx <- get
  ty' <- runReader ctx                                   (declare    (elab ty))
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
declare ty = goalIs type' ty >>= simplify

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
  Var a -> pure (Var a)
  Problem p -> case p of
    Lam t b -> do
      n <- gensym "lam"
      t' <- simplify t
      b' <- ForAll n ::: t' |- simplify (instantiate (pure (Local n)) b)
      pure (lam (Local n ::: t') b')
    f :$ a -> do
      f' <- simplify f
      a' <- simplify a
      pure (f' $$ a')
    Type -> pure type'
    Pi t b -> do
      n <- gensym "pi"
      t' <- simplify t
      b' <- ForAll n ::: t' |- simplify (instantiate (pure (Local n)) b)
      pure (pi (Local n ::: t') b')
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
        (Problem (Ex v1 t1 b1), Problem (Ex v2 t2 b2)) -> do
          n <- gensym "ex"
          t' <- simplify (t1 === t2)
          v' <- traverse simplify (v1 ?===? v2)
          (v'', b') <- (n ::: t') `bindMeta` simplify (instantiate (pure (Local n)) b1 === instantiate (pure (Local n)) b2)
          pure (exists (Local n := (v' <|> bindingValue v'') ::: t') b')
        (Problem (Ex v1 t1 b1), tm2) -> do
          n <- gensym "ex"
          t1' <- simplify t1
          v' <- traverse simplify v1
          (v'', tm1') <- (n ::: t1') `bindMeta` simplify (instantiate (pure (Local n)) b1 === tm2)
          pure (exists (Local n := (v' <|> bindingValue v'') ::: t1') tm1')
        (tm1, Problem (Ex v2 t2 b2)) -> do
          n <- gensym "ex"
          t2' <- simplify t2
          v' <- traverse simplify v2
          (v'', tm2') <- (n ::: t2') `bindMeta` simplify (tm1 === instantiate (pure (Local n)) b2)
          pure (exists (Local n := (v' <|> bindingValue v'') ::: t2') tm2')
        (Var (Local v1), t2) -> simplifyVar v1 t2
        (t1, Var (Local v2)) -> simplifyVar v2 t1
        (Problem (Pi t1 b1), Problem (Pi t2 b2)) -> do
          n <- gensym "pi"
          t' <- simplify (t1 === t2)
          ForAll n ::: t' |- pi (Local n ::: t') <$> simplify (instantiate (pure (Local n)) b1 === instantiate (pure (Local n)) b2)
        (Problem (Lam t1 b1), Problem (Lam t2 b2)) -> do
          n <- gensym "lam"
          t' <- simplify (t1 === t2)
          ForAll n ::: t' |- lam (Local n ::: t') <$> simplify (instantiate (pure (Local n)) b1 === instantiate (pure (Local n)) b2)
        (t1, t2) -> pure (Problem (t1 :===: t2))

simplifyVar :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Member (State Context) sig) => Gensym -> Problem (Name Gensym) -> m (Problem (Name Gensym))
simplifyVar v t = do
  v' <- lookupBinding (Local v)
  case v' of
    -- FIXME: occurs check
    Just (Exists (n := _) ::: _) -> pure (Local v) <$ solve (n := t)
    Just _ -> do
      p <- contextualize (Problem (pure (Local v) :===: t))
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


identity, identityT, constant, constantT, constantTQ :: Problem String

identity = lam ("A" ::: type') (lam ("a" ::: pure "A") (pure "a"))
identityT = pi ("A" ::: type') (pi ("_" ::: pure "A") (pure "A"))
constant = lam ("A" ::: type') (lam ("B" ::: type') (lam ("a" ::: pure "A") (lam ("b" ::: pure "B") (pure "a"))))
constantT = pi ("A" ::: type') (pi ("B" ::: type') (pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))

constantTQ
  = exists ("_A" := Nothing ::: type') (pi ("A" ::: pure "_A")
  ( exists ("_B" := Nothing ::: type') (pi ("B" ::: pure "_B")
  ( pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))))
