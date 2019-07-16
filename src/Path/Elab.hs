{-# LANGUAGE DeriveFunctor, FlexibleContexts, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Elab where

import Control.Applicative (liftA2)
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.Writer
import Control.Monad (foldM, join)
import Control.Monad.Trans
import Data.Bifunctor (first)
import Data.Foldable (foldl')
import Data.Functor.Const
import qualified Data.Map as Map
import Data.Void
import Path.Core
import Path.Error
import Path.Module as Module
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Problem
import Path.Scope
import Path.Span
import Path.Stack as Stack
import qualified Path.Surface as Surface
import Path.Syntax
import Path.Term
import Path.Usage
import Prelude hiding (pi)

assume :: ( Carrier sig m
          , Member (Error Doc) sig
          , Member (Reader Context) sig
          , Member (Reader Span) sig
          )
       => Qualified
       -> m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
assume v = asks (lookupBinding (Global v)) >>= maybe (freeVariables (pure v)) (pure . (Var (Global v) :::) . typedType)

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader Context) sig
         )
      => m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
      -> m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
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
      => m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
      -> m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
      -> m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
t --> body = do
  t' <- goalIs type' t
  x <- fresh
  b' <- ForAll x ::: t' |- goalIs type' body
  pure (pi (Local x ::: t') b' ::: type')

app :: ( Carrier sig m
       , Member Naming sig
       , Member (Reader Context) sig
       )
    => m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
    -> m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
    -> m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
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
       => Term (Problem :+: Core) (Name Gensym)
       -> m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
       -> m (Term (Problem :+: Core) (Name Gensym))
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- meta (ty1 === ty2)
  pure (tm1 === tm2)

meta :: (Carrier sig m, Member Naming sig) => Term (Problem :+: Core) (Name Gensym) -> m (Term (Problem :+: Core) (Name Gensym))
meta ty = do
  n <- fresh
  pure (exists (Local n ::: ty) (pure (Local n)))

(|-) :: (Carrier sig m, Member (Reader Context) sig) => Binding ::: Term (Problem :+: Core) (Name Gensym) -> m a -> m a
b |- m = local (:> b) m

infix 3 |-


elab :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member Naming sig
        , Member (Reader Context) sig
        , Member (Reader Span) sig
        )
     => Term Surface.Surface Qualified
     -> m (Term (Problem :+: Core) (Name Gensym) ::: Term (Problem :+: Core) (Name Gensym))
elab = kcata id alg bound assume
  where bound (Z _) = asks @Context (first (Var . bindingName) . Stack.head)
        bound (S m) = local @Context (Stack.drop 1) m
        alg = \case
          Surface.Lam _ b -> intro (elab' (unScope <$> b))
          f Surface.:$ (_ :< a) -> app (elab' f) (elab' a)
          Surface.Type -> pure (type' ::: type')
          Surface.Pi (_ :< _ ::: _ :@ t) b -> elab' t --> elab' (unScope <$> b)
        elab' = spanIs . fmap getConst

elabDecl :: ( Carrier sig m
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (Reader Context) sig
            , Member (Reader ModuleName) sig
            )
         => Decl (Term Surface.Surface Qualified)
         -> m (Decl (Term (Problem :+: Core) Qualified))
elabDecl (Decl name d tm ty) = namespace (show name) $ do
  ty' <- runSpanned (goalIs type' . elab) ty
  def <- meta (unSpanned ty')
  moduleName <- ask
  tm' <- runSpanned (local (:> Define (moduleName :.: name := def) ::: unSpanned ty') . goalIs (unSpanned ty') . elab) tm
  ty'' <- runSpanned (either freeVariables pure . strengthen) ty'
  tm'' <- runSpanned (either freeVariables pure . strengthen) tm'
  pure (Decl name d tm'' ty'')

elabModule :: ( Carrier sig m
              , Member (Error Doc) sig
              , Member Naming sig
              , Member (Reader (ModuleGraph (Term (Problem :+: Core)) Void)) sig
              , Member (Writer (Stack Doc)) sig
              )
           => Module (Term Surface.Surface) Qualified
           -> m (Module (Term (Problem :+: Core)) Qualified)
elabModule m = namespace (show (moduleName m)) . runReader (moduleName m) . local @(ModuleGraph (Term (Problem :+: Core)) Void) (Module.restrict (Map.keysSet (moduleImports m))) $ do
  -- FIXME: do a topo sort on the decls? or at least make their types known first? or…?
  decls <- foldM go mempty (moduleDecls m)
  pure m { moduleDecls = decls }
  where go decls decl = local (extendGraph decls) . inContext $ do
          (extendModule decls <$> elabDecl (instantiate (pure . qualified . (moduleDecls m Map.!)) <$> decl)) `catchError` ((decls <$) . logError)
        extendModule decls decl = Map.insert (declName decl) (bind (Just . unqualified) <$> decl) decls
        extendGraph decls (ModuleGraph g) = ModuleGraph @(Term (Problem :+: Core)) @Void (Map.insert (moduleName m) (bindHEither Left m { moduleDecls = decls }) g)
        qualified = (moduleName m :.:) . declName
        unqualified (_ :.: u) = u

inContext :: (Carrier sig m, Member (Reader (ModuleGraph (Term (Problem :+: Core)) Void)) sig)
          => ReaderC Context m a
          -> m a
inContext m = do
  ctx <- asks @(ModuleGraph (Term (Problem :+: Core)) Void) toContext
  runReader @Context ctx m
  where toContext g = foldl' definitions Nil (modules g)
        definitions ctx m = foldl' define ctx (moduleDecls m)
          where define ctx d = ctx :> (Define ((moduleName m :.: declName d) := inst (declTerm d)) ::: inst (declType d))
                inst t = instantiateEither (pure . Global . either (moduleName m :.:) id) (unSpanned t)

logError :: (Member (Writer (Stack Doc)) sig, Carrier sig m) => Doc -> m ()
logError = tell . (Nil :>)


type Context = Stack (Binding ::: Term (Problem :+: Core) (Name Gensym))


data Binding
  = Define (Qualified := Term (Problem :+: Core) (Name Gensym))
  | Exists (Gensym := Maybe (Term (Problem :+: Core) (Name Gensym)))
  | ForAll Gensym
  deriving (Eq, Ord, Show)

bindingName :: Binding -> Name Gensym
bindingName (Define (n := _)) = Global n
bindingName (Exists (n := _)) = Local n
bindingName (ForAll  n)       = Local n

bindingValue :: Binding -> Maybe (Term (Problem :+: Core) (Name Gensym))
bindingValue (Define (_ := v)) = Just v
bindingValue (Exists (_ := v)) = v
bindingValue (ForAll  _)       = Nothing

lookupBinding :: Name Gensym -> Context -> Maybe (Binding ::: Term (Problem :+: Core) (Name Gensym))
lookupBinding n = Stack.find ((== n) . bindingName . typedTerm)


newtype SolverC m a = SolverC { runSolverC :: m (Term Core a) }
  deriving (Functor)

instance Applicative m => Applicative (SolverC m) where
  pure = SolverC . pure . Var
  SolverC f <*> SolverC a = SolverC (liftA2 (<*>) f a)

instance Monad m => Monad (SolverC m) where
  SolverC a >>= f = SolverC (a >>= fmap join . traverse (runSolverC . f))

instance MonadTrans SolverC where
  lift = SolverC . fmap Var


identity, identityT, constant, constantT, constantTQ :: Term (Problem :+: Core) String

identity = lam "A" (lam "a" (pure "a"))
identityT = pi ("A" ::: type') (pi ("_" ::: pure "A") (pure "A"))
constant = lam "A" (lam "B" (lam "a" (lam "b" (pure "a"))))
constantT = pi ("A" ::: type') (pi ("B" ::: type') (pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))

constantTQ
  = exists ("_A" ::: type') (pi ("A" ::: pure "_A")
  ( exists ("_B" ::: type') (pi ("B" ::: pure "_B")
  ( pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))))
