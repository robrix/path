{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, KindSignatures, MultiParamTypeClasses, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Effect.Sum
import Control.Effect.Writer
import Control.Monad ((<=<))
import Data.Foldable (foldl', for_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Path.Stack as Stack
import Path.Constraint hiding (Scope(..), (|-))
import Path.Context as Context
import qualified Path.Core as Core
import Path.Eval
import Path.Module
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Scope as Scope
import Path.Semiring
import Path.Solver
import Path.Usage
import Path.Value (Type, Value(..))
import qualified Path.Value as Value
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span(..), Spanned(..))

assume :: (Carrier sig m, Member Elab sig, Member Naming sig)
       => Name Gensym
       -> m (Value Meta ::: Type Meta)
assume v = do
  _A <- have v
  implicits _A >>= foldl' app (pure (name (pure . Name) Value.global v ::: _A))

implicits :: (Carrier sig m, Member Elab sig) => Type Meta -> m (Stack (Plicit (m (Value Meta ::: Type Meta))))
implicits = go Nil
  where go names (Value.Pi (Im :< (_, t)) b) | False = do
          v <- exists t
          go (names :> (Im :< pure (v ::: t))) (Value.instantiate v b)
        go names _ = pure names

intro :: (Carrier sig m, Member Elab sig, Member Naming sig)
      => Plicit (Maybe User)
      -> (Gensym -> m (Value Meta ::: Type Meta))
      -> m (Value Meta ::: Type Meta)
intro (p :< x) body = do
  _A <- exists Type
  x <- gensym (maybe "_" showUser x)
  _B <- x ::: _A |- exists Type
  u <- x ::: _A |- goalIs _B (body x)
  pure (Value.lam (p :< Name x) u ::: Value.pi (p :< (Name x, More) ::: _A) _B)

pi :: (Carrier sig m, Member Elab sig, Member Naming sig)
   => Plicit (Maybe User, Usage, m (Value Meta ::: Type Meta))
   -> (Gensym -> m (Value Meta ::: Type Meta))
   -> m (Value Meta ::: Type Meta)
pi (p :< (x, m, t)) body = do
  t' <- goalIs Type t
  x <- gensym (maybe "_" showUser x)
  b' <- x ::: t' |- goalIs Type (body x)
  pure (Value.pi (p :< (Name x, m) ::: t') b' ::: Type)

app :: (Carrier sig m, Member Elab sig, Member Naming sig)
    => m (Value Meta ::: Type Meta)
    -> Plicit (m (Value Meta ::: Type Meta))
    -> m (Value Meta ::: Type Meta)
app f (p :< a) = do
  _A <- exists Type
  x <- gensym "app"
  _B <- x ::: _A |- exists Type
  let _F = Value.pi (p :< (Name x, case p of { Im -> zero ; Ex -> More }) ::: _A) _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' Value.$$ (p :< a') ::: _F Value.$$ (p :< a'))


exists :: (Carrier sig m, Member Elab sig)
       => Type Meta
       -> m (Value Meta)
exists ty = send (Exists ty pure)

goalIs :: (Carrier sig m, Member Elab sig) => Type Meta -> m (Value Meta ::: Type Meta) -> m (Value Meta)
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- exists ty2
  tm2 <$ unify (tm1 ::: ty1 :===: tm2 ::: ty2)

unify :: (Carrier sig m, Member Elab sig)
      => Equation (Value Meta ::: Type Meta)
      -> m ()
unify q = send (Unify q (pure ()))

(|-) :: (Carrier sig m, Member Elab sig) => Gensym ::: Type Meta -> m a -> m a
b |- m = send (Bind b m pure)

infix 5 |-

have :: (Carrier sig m, Member Elab sig) => Name Gensym -> m (Type Meta)
have n = send (Have n pure)


spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)

elab :: (Carrier sig m, Member Elab sig, Member Naming sig, Member (Reader Span) sig)
     => Core.Core Gensym
     -> m (Value Meta ::: Type Meta)
elab = \case
  Core.Var n -> assume n
  Core.Lam n b -> intro n (\ n' -> elab (Core.instantiate (pure n') b))
  f Core.:$ (p :< a) -> app (elab f) (p :< elab a)
  Core.Type -> pure (Type ::: Type)
  Core.Pi m t (Core.Lam (p :< n) b) -> pi (p :< (n, m, elab t)) (\ n' -> elab (Core.instantiate (pure n') b))
  Core.Pi m t b -> pi (Ex :< (Nothing, m, elab t)) (\ _ -> elab b)
  Core.Hole h -> (pure (Meta h) :::) <$> exists Type
  Core.Ann ann b -> spanIs ann (elab b)


data Elab m k
  = Exists (Type Meta) (Value Meta -> k)
  | Have (Name Gensym) (Type Meta -> k)
  | forall a . Bind (Gensym ::: Type Meta) (m a) (a -> k)
  | Unify (Equation (Value Meta ::: Type Meta)) k

deriving instance Functor (Elab m)

instance HFunctor Elab where
  hmap f = \case
    Exists t   k -> Exists t       k
    Have   n   k -> Have   n       k
    Bind   b m k -> Bind   b (f m) k
    Unify  q   k -> Unify  q       k

instance Effect Elab where
  handle state handler = \case
    Exists t   k -> Exists t                        (handler . (<$ state) . k)
    Have   n   k -> Have   n                        (handler . (<$ state) . k)
    Bind   b m k -> Bind   b (handler (m <$ state)) (handler . fmap k)
    Unify  q   k -> Unify  q                        (handler (k <$ state))


runElab :: ElabC m a -> m (Set.Set (Spanned (Constraint Meta)), a)
runElab = runWriter . runReader mempty . runElabC

newtype ElabC m a = ElabC { runElabC :: ReaderC (Context (Type Meta)) (WriterC (Set.Set (Spanned (Constraint Meta))) m) a }
  deriving (Applicative, Functor, Monad)

instance (Carrier sig m, Effect sig, Member Naming sig, Member (Reader Scope) sig, Member (Reader Span) sig, Member (State Signature) sig) => Carrier (Elab :+: sig) (ElabC m) where
  eff (L (Exists ty k)) = do
    ctx <- ElabC ask
    n <- gensym "meta"
    let f (n ::: t) = Ex :< (Name n, More) ::: t
        ty' = Value.pis (f <$> Context.unContext ctx) ty
    modify (Signature . Map.insert n ty' . unSignature)
    k (pure (Meta n) Value.$$* ((Ex :<) . pure . Name <$> Context.vars (ctx :: Context (Type Meta))))
  eff (L (Have n k)) = lookup n >>= maybe missing pure >>= k
    where lookup (Global n) = ElabC (asks (Scope.lookup   n)) >>= pure . fmap (Value.weaken . entryType)
          lookup (Local  n) = ElabC (asks (Context.lookup n))
          missing = do
            ty <- exists Type
            tm <- exists ty
            ty <$ unify (tm ::: ty :===: name (pure . Name) Value.global n ::: ty)
  eff (L (Bind (n ::: t) m k)) = ElabC (local (Context.insert (n ::: t)) (runElabC m)) >>= k
  eff (L (Unify (tm1 ::: ty1 :===: tm2 ::: ty2) k)) = ElabC $ do
    span <- ask
    context <- ask
    tell (Set.fromList
      [ (binds context ((ty1 :===: ty2) ::: Value.Type)) :~ span
      , (binds context ((tm1 :===: tm2) ::: ty1))        :~ span
      ])
    runElabC k
  eff (R other) = ElabC (eff (R (R (handleCoercible other))))

inferType :: (Carrier sig m, Member Naming sig) => m (Type Meta)
inferType = pure . Meta <$> gensym "meta"


type ModuleTable = Map.Map ModuleName Scope

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error Doc) sig
              , Member Naming sig
              , Member (Reader ModuleTable) sig
              , Member (State (Stack Doc)) sig
              , Member (State Scope) sig
              )
           => Module Qualified (Core.Core Gensym ::: Core.Core Gensym)
           -> m (Module Qualified (Value Gensym ::: Type Gensym))
elabModule m = namespace (show (moduleName m)) $ do
  for_ (moduleImports m) (modify . Scope.union <=< importModule)

  decls <- for (moduleDecls m) $ \ decl ->
    (Just <$> elabDecl decl) `catchError` ((Nothing <$) . logError)
  pure m { moduleDecls = catMaybes decls }

logError :: (Member (State (Stack Doc)) sig, Carrier sig m) => Doc -> m ()
logError = modify . flip (:>)

importModule :: ( Carrier sig m
                , Member (Error Doc) sig
                , Member (Reader ModuleTable) sig
                )
             => Spanned Import
             -> m Scope
importModule n@(i :~ _) = asks (Map.lookup (importModuleName i)) >>= maybe (unknownModule n) pure


elabDecl :: ( Carrier sig m
            , Effect sig
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (State Scope) sig
            )
         => Spanned (Decl Qualified (Core.Core Gensym ::: Core.Core Gensym))
         -> m (Spanned (Decl Qualified (Value Gensym ::: Type Gensym)))
elabDecl (Decl d name (tm ::: ty) :~ span) = namespace (show name) . runReader span . fmap (:~ span) $ do
  ty' <- runScope (declare (elab ty))
  modify (Scope.insert name (Entry (Nothing ::: ty')))
  scope <- get

  let ty'' = whnf scope ty'
  (names, _) <- un (orTerm (\ n -> \case
    Value.Pi (Im :< _) b | False -> Just (Im :< n, whnf scope (Value.instantiate (pure n) b))
    _                    -> Nothing)) ty''
  tm ::: _ <- runScope (define (Value.weaken ty') (elab (Core.lams names tm)))
  modify (Scope.insert name (Entry (Just tm ::: ty')))
  pure (Decl d name (tm ::: ty'))

declare :: ( Carrier sig m
           , Effect sig
           , Member (Error Doc) sig
           , Member Naming sig
           , Member (Reader Scope) sig
           , Member (Reader Span) sig
           )
        => ElabC (StateC Signature m) (Value Meta ::: Type Meta)
        -> m (Value Gensym)
declare ty = evalState (mempty :: Signature) $ do
  (constraints, ty') <- runElab (goalIs Type ty)
  subst <- solver constraints
  pure (Value.generalizeType (apply subst ty'))

define :: ( Carrier sig m
          , Effect sig
          , Member (Error Doc) sig
          , Member Naming sig
          , Member (Reader Scope) sig
          , Member (Reader Span) sig
          )
       => Value Meta
       -> ElabC (StateC Signature m) (Value Meta ::: Type Meta)
       -> m (Value Gensym ::: Type Gensym)
define ty tm = evalState (mempty :: Signature) $ do
  (constraints, tm') <- runElab (goalIs ty tm)
  subst <- solver constraints
  let ty' = Value.generalizeType (apply subst ty)
  (::: ty') <$> Value.strengthen (apply subst tm')

runScope :: (Carrier sig m, Member (State Scope) sig) => ReaderC Scope m a -> m a
runScope m = get >>= flip runReader m
