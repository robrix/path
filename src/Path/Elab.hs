{-# LANGUAGE DataKinds, DeriveFunctor, FlexibleContexts, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Elab where

import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Control.Effect.Writer
import Control.Monad ((<=<), foldM)
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable
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
          , Member (Error Notice) sig
          , Member (Reader Globals) sig
          , Member (Reader Excerpt) sig
          )
       => Qualified
       -> m (Term (Problem :+: Core) (Var (Fin n) Qualified) ::: Term (Problem :+: Core) (Var (Fin n) Qualified))
assume v = asks (Stack.find ((== v) . typedTerm)) >>= maybe (freeVariables (pure v)) (pure . (Var (F v) :::) . hoistTerm R . fmap F . typedType)

intro :: Monad m
      => (Term (Problem :+: Core) (Var (Fin ('S n)) a) -> m (Term (Problem :+: Core) (Var (Fin ('S n)) a) ::: Term (Problem :+: Core) (Var (Fin ('S n)) a)))
      -> m (Term (Problem :+: Core) (Var (Fin n) a) ::: Term (Problem :+: Core) (Var (Fin n) a))
intro body = do
  let _A = meta type'
      _B = meta type'
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
  let _A = meta type'
      _B = meta type'
      _F = piFin _A _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' $$ a' ::: _F $$ a')


goalIs :: Monad m
       => Term (Problem :+: Core) (Var (Fin n) a)
       -> m (Term (Problem :+: Core) (Var (Fin n) a) ::: Term (Problem :+: Core) (Var (Fin n) a))
       -> m (Term (Problem :+: Core) (Var (Fin n) a))
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  let tm2 = meta (ty1 === ty2)
  pure (tm1 === tm2)

meta
  :: Term (Problem :+: Core) (Var (Fin n) a)
  -> Term (Problem :+: Core) (Var (Fin n) a)
meta ty = existsFin ty (pure (B FZ))


elab
  :: ( Carrier sig m
     , Member (Error Notice) sig
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
            , Effect sig
            , Member (Error Notice) sig
            , Member (Reader Globals) sig
            , Member (Reader ModuleName) sig
            )
         => Decl (Term Surface.Surface Qualified)
         -> m (Decl (Term Core Qualified))
elabDecl (Decl name d tm ty) = do
  ty' <- runSpanned (fmap strengthen . solve VZ <=< goalIs type' . elab VZ . fmap F) ty
  moduleName <- ask
  tm' <- runSpanned (fmap strengthen . solve VZ <=< local (:> (moduleName :.: name) ::: unSpanned ty') . goalIs (hoistTerm R (F <$> unSpanned ty')) . elab VZ . fmap F) tm
  pure (Decl name d tm' ty')

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error Notice) sig
              , Member (Reader (ModuleGraph (Term Core) Void)) sig
              , Member (Writer (Stack Notice)) sig
              )
           => Module (Term Surface.Surface) Qualified
           -> m (Module (Term Core) Qualified)
elabModule m = runReader (moduleName m) . local @(ModuleGraph (Term Core) Void) (Module.restrict (Map.keysSet (moduleImports m))) $ do
  -- FIXME: do a topo sort on the decls? or at least make their types known first? or…?
  decls <- foldM go mempty (moduleDecls m)
  pure m { moduleDecls = decls }
  where go decls decl = local (extendGraph decls) . withGlobals $ do
          (extendModule decls <$> elabDecl (instantiate (pure . qualified . (moduleDecls m Map.!)) <$> decl)) `catchError` ((decls <$) . logError)
        extendModule decls decl = Map.insert (declName decl) (bind (Just . unqualified) <$> decl) decls
        extendGraph decls (ModuleGraph g) = ModuleGraph @(Term Core) @Void (Map.insert (moduleName m) (bindTEither Left m { moduleDecls = decls }) g)
        qualified = (moduleName m :.:) . declName
        unqualified (_ :.: u) = u

withGlobals
  :: (Carrier sig m, Member (Reader (ModuleGraph (Term Core) Void)) sig)
  => ReaderC Globals m a
  -> m a
withGlobals m = do
  ctx <- asks @(ModuleGraph (Term Core) Void) toContext
  runReader @Globals ctx m
  where toContext g = foldl' definitions Nil (modules g)
        definitions ctx m = foldl' define ctx (moduleDecls m)
          where define ctx d = ctx :> (moduleName m :.: declName d) ::: inst (declType d)
                inst t = instantiateEither (pure . either (moduleName m :.:) id) (unSpanned t)

logError :: (Member (Writer (Stack Notice)) sig, Carrier sig m) => Notice -> m ()
logError = tell . (Nil :>)


type Globals = Stack (Qualified ::: Term Core Qualified)


solve
  :: ( Carrier sig m
     , Effect sig
     , Eq a
     , Member (Error Notice) sig
     , Member (Reader Excerpt) sig
     , Pretty a
     )
  => Vec n Bool
  -> Term (Problem :+: Core) (Var (Fin n) a)
  -> m (Term Core (Var (Fin n) a))
solve ctx = \case
  Var v -> pure (Var v)
  Term (L p) -> case p of
    Ex t b -> do
      _ <- solve ctx t
      -- push the fact that this is a metavar
      (soln, b') <- runState Nothing (solve (VS True ctx) (fromScopeFin b))
      case traverse (bitraverse strengthenFin Just) b' of
        Just b' -> pure b' -- the existential isn’t used, so there’s nothing to solve for
        -- check to see if we have a solution or not
        Nothing -> case soln of
          Just soln' -> pure (Term (Let soln' (toScopeFin b')))
          -- FIXME: float if necessary
          Nothing    -> ask >>= \ e -> throwError (Notice (Just Error) e (pretty "no local solution") [])
    Unify q -> simplify ctx q
  Term (R c) -> case c of
    Lam   b -> lamFin <$>                 solve (VS False ctx) (fromScopeFin b)
    f :$ a  -> ($$) <$> solve ctx f <*> solve ctx a
    Let v b -> letFin <$> solve ctx v <*> solve (VS False ctx) (fromScopeFin b)
    Type    -> pure type'
    Pi  t b -> piFin  <$> solve ctx t <*> solve (VS False ctx) (fromScopeFin b)

simplify
  :: ( Carrier sig m
     , Effect sig
     , Eq a
     , Member (Error Notice) sig
     , Member (Reader Excerpt) sig
     , Pretty a
     )
  => Vec n Bool
  -> Equation (Term (Problem :+: Core) (Var (Fin n) a))
  -> m (Term Core (Var (Fin n) a))
simplify ctx = \case
  Term (R (Lam    b1)) :===: Term (R (Lam    b2)) -> Term . Lam . toScopeFin <$> solve (VS False ctx) (fromScopeFin b1 === fromScopeFin b2)
  -- Term (R (f1 :$ a1))  :===: Term (R (f2 :$ a2))  -> _ -- FIXME: do some sort of unapplies thing and hereditary substitution to get to this point
  Term (R (Let v1 b1)) :===: Term (R (Let v2 b2)) -> Term <$> (Let <$> solve ctx (v1 === v2) <*> (toScopeFin <$> solve (VS False ctx) (fromScopeFin b1 === fromScopeFin b2)))
  Term (R (Pi  t1 b1)) :===: Term (R (Pi  t2 b2)) -> Term <$> (Pi <$> solve ctx (t1 === t2) <*> (toScopeFin <$> solve (VS False ctx) (fromScopeFin b1 === fromScopeFin b2)))
  p1 :===: p2 -> do
    p1' <- solve ctx p1
    p2' <- solve ctx p2
    if p1' == p2' then
      pure p1'
    else
      unsolvableConstraint p1' p2'


identity, identityT, constant, constantT, constantTQ :: Term (Problem :+: Core) String

identity = lam "A" (lam "a" (pure "a"))
identityT = pi ("A" ::: type') (pi ("_" ::: pure "A") (pure "A"))
constant = lam "A" (lam "B" (lam "a" (lam "b" (pure "a"))))
constantT = pi ("A" ::: type') (pi ("B" ::: type') (pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))

constantTQ
  = exists ("_A" ::: type') (pi ("A" ::: pure "_A")
  ( exists ("_B" ::: type') (pi ("B" ::: pure "_B")
  ( pi ("_" ::: pure "A") (pi ("_" ::: pure "B") (pure "A"))))))
