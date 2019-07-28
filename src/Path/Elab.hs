{-# LANGUAGE DataKinds, DeriveFunctor, FlexibleContexts, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Elab where

import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.Writer
import Control.Monad (foldM)
import Data.Bifunctor (Bifunctor (..))
import Data.Foldable (foldl')
import qualified Data.Map as Map
import Data.Void
import Path.Core
import Path.Error
import Path.Module as Module
import Path.Name
import Path.Plicity (Plicit (..))
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
          , Member (Reader Globals) sig
          , Member (Reader Excerpt) sig
          )
       => Qualified
       -> m (Term (Problem :+: Core) (Var (Fin n) Qualified) ::: Term (Problem :+: Core) (Var (Fin n) Qualified))
assume v = asks (Stack.find ((== v) . typedTerm)) >>= maybe (freeVariables (pure v)) (pure . (Var (F v) :::) . fmap F . typedType)

intro :: Monad m
      => (Term (Problem :+: Core) (Var (Fin ('S n)) a) -> m (Term (Problem :+: Core) (Var (Fin ('S n)) a) ::: Term (Problem :+: Core) (Var (Fin ('S n)) a)))
      -> m (Term (Problem :+: Core) (Var (Fin n) a) ::: Term (Problem :+: Core) (Var (Fin n) a))
intro body = do
  _A <- meta type'
  _B <- meta type'
  u <- goalIs _B (body (first FS <$> _A))
  pure (lamFin u ::: piFin _A _B)

(-->) :: Monad m
      => m (Term (Problem :+: Core) (Var (Fin n) a) ::: Term (Problem :+: Core) (Var (Fin n) a))
      -> (Term (Problem :+: Core) (Var (Fin ('S n)) a) -> m (Term (Problem :+: Core) (Var (Fin ('S n)) a) ::: Term (Problem :+: Core) (Var (Fin ('S n)) a)))
      -> m (Term (Problem :+: Core) (Var (Fin n) a) ::: Term (Problem :+: Core) (Var (Fin n) a))
t --> body = do
  t' <- goalIs type' t
  b' <- goalIs type' (body (first FS <$> t'))
  pure (piFin t' b' ::: type')

app :: Monad m
    => m (Term (Problem :+: Core) (Var (Fin n) a) ::: Term (Problem :+: Core) (Var (Fin n) a))
    -> m (Term (Problem :+: Core) (Var (Fin n) a) ::: Term (Problem :+: Core) (Var (Fin n) a))
    -> m (Term (Problem :+: Core) (Var (Fin n) a) ::: Term (Problem :+: Core) (Var (Fin n) a))
app f a = do
  _A <- meta type'
  _B <- meta type'
  let _F = piFin _A _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' $$ a' ::: _F $$ a')


goalIs :: Monad m
       => Term (Problem :+: Core) (Var (Fin n) a)
       -> m (Term (Problem :+: Core) (Var (Fin n) a) ::: Term (Problem :+: Core) (Var (Fin n) a))
       -> m (Term (Problem :+: Core) (Var (Fin n) a))
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- meta (ty1 === ty2)
  pure (tm1 === tm2)

meta
  :: Monad m
  => Term (Problem :+: Core) (Var (Fin n) a)
  -> m (Term (Problem :+: Core) (Var (Fin n) a))
meta ty = pure (Term (L (Ex ty (toScopeFin (pure (B FZ))))))


elab
  :: ( Carrier sig m
     , Member (Error Doc) sig
     , Member (Reader Globals) sig
     , Member (Reader Excerpt) sig
     )
  => Vec n (Term (Problem :+: Core) (Var (Fin n) Qualified))
  -> Term Surface.Surface (Var (Fin n) Qualified)
  -> m (Term (Problem :+: Core) (Var (Fin n) Qualified) ::: Term (Problem :+: Core) (Var (Fin n) Qualified))
elab ctx = \case
    Var (B n) -> pure (pure (B n) ::: ctx ! n)
    Var (F n) -> assume n
    Term t -> case t of
      Surface.Lam _ b -> intro (\ t -> elab' (VS t (fmap (first FS) <$> ctx)) (fromScopeFin <$> b))
      f Surface.:$ (_ :< a) -> app (elab' ctx f) (elab' ctx a)
      Surface.Type -> pure (type' ::: type')
      Surface.Pi (_ :< _ ::: t) b -> elab' ctx t --> \ t' -> elab' (VS t' (fmap (first FS) <$> ctx)) (fromScopeFin <$> b)
  where elab' ctx m = spanIs (elab ctx <$> m)

elabDecl :: ( Carrier sig m
            , Member (Error Doc) sig
            , Member (Reader Globals) sig
            , Member (Reader ModuleName) sig
            )
         => Decl (Term Surface.Surface Qualified)
         -> m (Decl (Term (Problem :+: Core) Qualified))
elabDecl (Decl name d tm ty) = do
  ty' <- runSpanned (fmap strengthen . goalIs type' . elab VZ . fmap F) ty
  moduleName <- ask
  tm' <- runSpanned (fmap strengthen . local (:> (moduleName :.: name) ::: unSpanned ty') . goalIs (F <$> unSpanned ty') . elab VZ . fmap F) tm
  pure (Decl name d tm' ty')
  where strengthen :: Term (Problem :+: Core) (Var (Fin 'Z) Qualified) -> Term (Problem :+: Core) Qualified
        strengthen = fmap (var absurdFin id)

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
  where go decls decl = local (extendGraph decls) . withGlobals $ do
          (extendModule decls <$> elabDecl (instantiate (pure . qualified . (moduleDecls m Map.!)) <$> decl)) `catchError` ((decls <$) . logError)
        extendModule decls decl = Map.insert (declName decl) (bind (Just . unqualified) <$> decl) decls
        extendGraph decls (ModuleGraph g) = ModuleGraph @(Term (Problem :+: Core)) @Void (Map.insert (moduleName m) (bindTEither Left m { moduleDecls = decls }) g)
        qualified = (moduleName m :.:) . declName
        unqualified (_ :.: u) = u

withGlobals
  :: (Carrier sig m, Member (Reader (ModuleGraph (Term (Problem :+: Core)) Void)) sig)
  => ReaderC Globals m a
  -> m a
withGlobals m = do
  ctx <- asks @(ModuleGraph (Term (Problem :+: Core)) Void) toContext
  runReader @Globals ctx m
  where toContext g = foldl' definitions Nil (modules g)
        definitions ctx m = foldl' define ctx (moduleDecls m)
          where define ctx d = ctx :> (moduleName m :.: declName d) ::: inst (declType d)
                inst t = instantiateEither (pure . either (moduleName m :.:) id) (unSpanned t)

logError :: (Member (Writer (Stack Doc)) sig, Carrier sig m) => Doc -> m ()
logError = tell . (Nil :>)


type Globals = Stack (Qualified ::: Term (Problem :+: Core) Qualified)


identity, identityT, constant, constantT, constantTQ :: Term (Problem :+: Core) String

identity = lam "A" (lam "a" (pure "a"))
identityT = pi ("A" ::: type') (pi ("_" ::: pure "A") (pure "A"))
constant = lam "A" (lam "B" (lam "a" (lam "b" (pure "a"))))
constantT = pi ("A" ::: type') (pi ("B" ::: type') (pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))

constantTQ
  = exists ("_A" ::: type') (pi ("A" ::: pure "_A")
  ( exists ("_B" ::: type') (pi ("B" ::: pure "_B")
  ( pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))))
