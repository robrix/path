{-# LANGUAGE DeriveFunctor, FlexibleContexts, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Elab where

import Control.Applicative (liftA2)
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.Writer
import Control.Monad ((<=<), foldM, join)
import Control.Monad.Trans
import Data.Foldable (foldl')
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
import Prelude hiding (pi)

assume :: ( Carrier sig m
          , Member (Error Doc) sig
          , Member (Reader Context) sig
          , Member (Reader Excerpt) sig
          )
       => Qualified
       -> m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N))
assume v = asks (lookupBinding v) >>= maybe (freeVariables (pure v)) (pure . (Var (Global v) :::) . typedType)

intro :: ( Carrier sig m
         , Member (Reader N) sig
         )
      => (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N) -> m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N)))
      -> m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N))
intro body = do
  _A <- meta type'
  _B <- meta type'
  bindN $ \ x -> do
    u <- goalIs _B (body (pure (Local x) ::: _A))
    pure (lam (Local x) u ::: pi (Local x ::: _A) _B)

(-->) :: ( Carrier sig m
         , Member (Reader N) sig
         )
      => m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N))
      -> (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N) -> m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N)))
      -> m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N))
t --> body = do
  t' <- goalIs type' t
  bindN $ \ x -> do
    b' <- goalIs type' (body (pure (Local x) ::: t'))
    pure (pi (Local x ::: t') b' ::: type')

app :: ( Carrier sig m
       , Member (Reader N) sig
       )
    => m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N))
    -> m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N))
    -> m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N))
app f a = do
  _A <- meta type'
  x <- ask @N
  _B <- meta type'
  let _F = pi (Local x ::: _A) _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' $$ a' ::: _F $$ a')


goalIs :: ( Carrier sig m
          , Member (Reader N) sig
          )
       => Term (Problem :+: Core) (Name N)
       -> m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N))
       -> m (Term (Problem :+: Core) (Name N))
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- meta (ty1 === ty2)
  pure (tm1 === tm2)

meta :: (Carrier sig m, Member (Reader N) sig) => Term (Problem :+: Core) (Name N) -> m (Term (Problem :+: Core) (Name N))
meta ty = do
  n <- ask @N
  pure (exists (Local n ::: ty) (pure (Local n)))


elab :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member (Reader Context) sig
        , Member (Reader N) sig
        , Member (Reader Excerpt) sig
        )
     => Term Surface.Surface Qualified
     -> m (Term (Problem :+: Core) (Name N) ::: Term (Problem :+: Core) (Name N))
elab = go <=< traverse assume
  where go = \case
          Var v -> pure v
          Term t -> case t of
            Surface.Lam _ b -> intro (\ t -> elab' (instantiate1 (pure t) <$> b))
            f Surface.:$ (_ :< a) -> app (elab' f) (elab' a)
            Surface.Type -> pure (type' ::: type')
            Surface.Pi (_ :< _ ::: t) b -> elab' t --> \ t' -> elab' (instantiate1 (pure t') <$> b)
        elab' m = spanIs (go <$> m)

elabDecl :: ( Carrier sig m
            , Member (Error Doc) sig
            , Member (Reader Context) sig
            , Member (Reader ModuleName) sig
            )
         => Decl (Term Surface.Surface Qualified)
         -> m (Decl (Term (Problem :+: Core) Qualified))
elabDecl (Decl name d tm ty) = runReader (N 0) $ do
  ty' <- runSpanned (goalIs type' . elab) ty
  def <- meta (unSpanned ty')
  moduleName <- ask
  tm' <- runSpanned (local (:> Define (moduleName :.: name := def) ::: unSpanned ty') . goalIs (unSpanned ty') . elab) tm
  ty'' <- runSpanned (either freeVariables pure . strengthen) ty'
  tm'' <- runSpanned (either freeVariables pure . strengthen) tm'
  pure (Decl name d tm'' ty'')

elabModule :: ( Carrier sig m
              , Member (Error Doc) sig
              , Member (Reader (ModuleGraph (Term (Problem :+: Core)) Void)) sig
              , Member (Writer (Stack Doc)) sig
              )
           => Module (Term Surface.Surface) Qualified
           -> m (Module (Term (Problem :+: Core)) Qualified)
elabModule m = runReader (moduleName m) . local @(ModuleGraph (Term (Problem :+: Core)) Void) (Module.restrict (Map.keysSet (moduleImports m))) $ do
  -- FIXME: do a topo sort on the decls? or at least make their types known first? or…?
  decls <- foldM go mempty (moduleDecls m)
  pure m { moduleDecls = decls }
  where go decls decl = local (extendGraph decls) . inContext $ do
          (extendModule decls <$> elabDecl (instantiate (pure . qualified . (moduleDecls m Map.!)) <$> decl)) `catchError` ((decls <$) . logError)
        extendModule decls decl = Map.insert (declName decl) (bind (Just . unqualified) <$> decl) decls
        extendGraph decls (ModuleGraph g) = ModuleGraph @(Term (Problem :+: Core)) @Void (Map.insert (moduleName m) (bindTEither Left m { moduleDecls = decls }) g)
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


type Context = Stack (Binding ::: Term (Problem :+: Core) (Name N))


data Binding
  = Define (Qualified := Term (Problem :+: Core) (Name N))
  | Exists (N := Maybe (Term (Problem :+: Core) (Name N)))
  | ForAll N
  deriving (Eq, Ord, Show)

bindingName :: Binding -> Name N
bindingName (Define (n := _)) = Global n
bindingName (Exists (n := _)) = Local n
bindingName (ForAll  n)       = Local n

bindingValue :: Binding -> Maybe (Term (Problem :+: Core) (Name N))
bindingValue (Define (_ := v)) = Just v
bindingValue (Exists (_ := v)) = v
bindingValue (ForAll  _)       = Nothing

lookupBinding :: Qualified -> Context -> Maybe (Binding ::: Term (Problem :+: Core) (Name N))
lookupBinding n = Stack.find ((== Global n) . bindingName . typedTerm)


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
