{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad (unless, when)
import Data.Foldable (for_)
import qualified Data.Map as Map
import Path.Context as Context
import Path.Core as Core
import Path.Decl
import Path.Env as Env
import Path.Eval
import Path.Module
import Path.Name
import Path.Pretty
import Path.Resources as Resources
import Path.Semiring
import Path.Surface as Surface
import Path.Term
import Path.Usage
import Path.Value
import Text.PrettyPrint.ANSI.Leijen
import Text.Trifecta.Rendering (Span, render)

elab :: ( Carrier sig m
        , Member (Error (ElabError v)) sig
        , Member (Reader (Context v)) sig
        , Member (Reader (Env v)) sig
        , Member (Reader Usage) sig
        , Monad m
        , Ord v
        , Show v
        )
     => Term (Surface v) Span
     -> Maybe (Type v)
     -> m (Term (Core v) (Resources v Usage, Type v))
elab (In (e ::: t) _) Nothing = do
  t' <- check t VType
  t'' <- asks (eval t')
  check e t''
elab (In (ForAll n t b) _) Nothing = do
  t' <- check t VType
  t'' <- asks (eval t')
  b' <- local (Context.insert n t'') (check (subst n (Surface.Var n) b) VType)
  pure (In (Core.Pi n Zero t' b') (Resources.empty, VType))
elab (In Surface.Type _) Nothing = pure (In Core.Type (Resources.empty, VType))
elab (In (Surface.Pi n e t b) _) Nothing = do
  t' <- check t VType
  t'' <- asks (eval t')
  b' <- local (Context.insert n t'') (check (subst n (Surface.Var n) b) VType)
  pure (In (Core.Pi n e t' b') (Resources.empty, VType))
elab (In (Surface.Var n) span) Nothing = do
  res <- asks (Context.lookup n)
  sigma <- ask
  case res of
    Just t -> pure (In (Core.Var n) (Resources.singleton n sigma, t))
    _      -> throwError (FreeVariable n span)
elab (In (f Surface.:@ a) _) Nothing = do
  f' <- infer f
  case ann f' of
    (g1, VPi _ pi t t') -> do
      a' <- check a t
      let (g2, _) = ann a'
      env <- ask
      pure (In (f' Core.:@ a') (g1 <> pi ><< g2, t' (eval a' env)))
    _ -> throwError (IllegalApplication f' (ann f))
elab tm Nothing = throwError (NoRuleToInfer tm (ann tm))
elab (In (Surface.Lam n e) span) (Just (VPi tn pi t t')) = do
  e' <- local (Context.insert n t) (check (subst n (Surface.Var n) e) (t' (vfree n)))
  let res = fst (ann e')
      used = Resources.lookup n res
  sigma <- ask
  unless (sigma >< pi == More) . when (pi /= used) $
    throwError (ResourceMismatch n pi used span (uses n e))
  pure (In (Core.Lam n e') (Resources.delete n res, VPi tn pi t t'))
elab tm (Just ty) = do
  v <- infer tm
  unless (snd (ann v) == ty) (throwError (TypeMismatch ty (snd (ann v)) (ann tm)))
  pure v

infer :: ( Carrier sig m
         , Member (Error (ElabError v)) sig
         , Member (Reader (Context v)) sig
         , Member (Reader (Env v)) sig
         , Member (Reader Usage) sig
         , Monad m
         , Ord v
         , Show v
         )
      => Term (Surface v) Span
      -> m (Term (Core v) (Resources v Usage, Type v))
infer tm = elab tm Nothing

check :: ( Carrier sig m
         , Member (Error (ElabError v)) sig
         , Member (Reader (Context v)) sig
         , Member (Reader (Env v)) sig
         , Member (Reader Usage) sig
         , Monad m
         , Ord v
         , Show v
         )
      => Term (Surface v) Span
      -> Type v
      -> m (Term (Core v) (Resources v Usage, Type v))
check tm = elab tm . Just


type ModuleTable = Map.Map ModuleName (Context Name, Env Name)

elabModule :: (Carrier sig m, Effect sig, Member (Error (ElabError Name)) sig, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig) => Module Name (Term (Surface Name) Span) -> m (Context Name, Env Name)
elabModule (Module _ imports decls) = runState Context.empty . execState (Env.empty :: Env Name) $ do
  for_ imports $ \ (Import name) -> do
    (ctx, env) <- importModule name
    modify (Context.union ctx)
    modify (Env.union env)

  for_ decls $ \case
    Declare name ty -> elabDecl name ty
    Define  name tm -> elabDef  name tm

importModule :: (Carrier sig m, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig, Monad m) => ModuleName -> m (Context Name, Env Name)
importModule n = asks (Map.lookup n) >>= maybe (throwError (UnknownModule n)) pure


elabDecl :: (Carrier sig m, Member (Error (ElabError Name)) sig, Member (State (Context Name)) sig, Member (State (Env Name)) sig, Monad m) => Name -> Term (Surface Name) Span -> m ()
elabDecl name ty = do
  ty' <- runInState Zero (check ty VType)
  ty'' <- gets (eval ty')
  modify (Context.insert name ty'')

elabDef :: (Carrier sig m, Member (Error (ElabError Name)) sig, Member (State (Context Name)) sig, Member (State (Env Name)) sig, Monad m) => Name -> Term (Surface Name) Span -> m ()
elabDef name tm = do
  ty <- gets (Context.lookup name)
  tm' <- runInState One (maybe infer (flip check) ty tm)
  tm'' <- gets (eval tm')
  modify (Env.insert name tm'')
  maybe (modify (Context.insert name (snd (ann tm')))) (const (pure ())) ty

runInState :: (Carrier sig m, Member (State (Context Name)) sig, Member (State (Env Name)) sig, Monad m) => Usage -> Eff (ReaderC (Context Name) (Eff (ReaderC (Env Name) (Eff (ReaderC Usage m))))) a -> m a
runInState usage m = do
  env <- get
  ctx <- get
  runReader usage (runReader env (runReader ctx m))


data ElabError v
  = FreeVariable v Span
  | TypeMismatch (Type v) (Type v) Span
  | NoRuleToInfer (Term (Surface v) Span) Span
  | IllegalApplication (Term (Core v) (Resources v Usage, Type v)) Span
  | ResourceMismatch v Usage Usage Span [Span]
  deriving (Eq, Ord, Show)

instance (Ord v, Pretty v) => Pretty (ElabError v) where
  pretty (FreeVariable name span) = nest 2 $ pretty "free variable" <+> squotes (pretty name) <$$> pretty (render span)
  pretty (TypeMismatch expected actual span) = nest 2 $ vsep
    [ pretty "type mismatch"
    , pretty "expected:" <+> pretty expected
    , pretty "  actual:" <+> pretty actual
    , pretty (render span)
    ]
  pretty (NoRuleToInfer _ span) = pretty "no rule to infer type of term" <$$> pretty (render span)
  pretty (IllegalApplication tm span) = pretty "illegal application of non-function term" <+> pretty tm <$$> pretty (render span)
  pretty (ResourceMismatch n pi used span spans) = nest 2 $ vsep
    ( pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length spans)) <+> pretty "than required" <+> parens (pretty pi)
    : if length spans == 0 then
        [ pretty (render span) ]
      else
        map (pretty . render) spans
    )

instance (Ord v, Pretty v) => PrettyPrec (ElabError v)

runElabError :: (Carrier sig m, Effect sig, Monad m) => Eff (ErrorC (ElabError Name) m) a -> m (Either (ElabError Name) a)
runElabError = runError
