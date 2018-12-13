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
import Path.Core
import Path.Decl
import Path.Eval
import Path.Module
import Path.Name
import Path.Pretty
import Path.Resources as Resources
import Path.Semiring
import Path.Surface
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen
import Text.Trifecta.Rendering (Span, render)

elab :: ( Carrier sig m
        , Member (Error ElabError) sig
        , Member (Reader Context) sig
        , Member (Reader Env) sig
        , Member (Reader Usage) sig
        , Monad m
        )
     => Term (Surface Name) Span
     -> Maybe Type
     -> m (Term (Core Name) (Resources Usage, Type))
elab (In (e ::: t) _) Nothing = do
  t' <- check t VType
  t'' <- asks (eval t')
  check e t''
elab (In (Core Type) _) Nothing = pure (In Type (Resources.empty, VType))
elab (In (Core (Pi n e t b)) _) Nothing = do
  t' <- check t VType
  t'' <- asks (eval t')
  b' <- case n of
    Just n -> local (Context.insert n t'') (check (subst n (Core (Var n)) b) VType)
    _      -> check b VType
  pure (In (Pi n e t' b') (Resources.empty, VType))
elab (In (Core (Var n)) span) Nothing = do
  res <- asks (Context.lookup n)
  sigma <- ask
  case res of
    Just t -> pure (In (Var n) (Resources.singleton n sigma, t))
    _      -> throwError (FreeVariable n span)
elab (In (Core (f :@ a)) _) Nothing = do
  f' <- infer f
  case ann f' of
    (g1, VPi _ pi t t') -> do
      a' <- check a t
      let (g2, _) = ann a'
      env <- ask
      pure (In (f' :@ a') (g1 <> pi ><< g2, t' (eval a' env)))
    _ -> throwError (IllegalApplication f' (ann f))
elab tm Nothing = throwError (NoRuleToInfer tm (ann tm))
elab (In (Core (Lam n e)) span) (Just (VPi tn pi t t')) = do
  e' <- case n of
    Just n -> do
      e' <- local (Context.insert n t) (check (subst n (Core (Var n)) e) (t' (vfree n)))
      sigma <- ask
      let used = Resources.lookup n (fst (ann e'))
      unless (sigma >< pi == More) . when (pi /= used) $
        throwError (ResourceMismatch (getName n) pi used span (uses n e))
      pure e'
    _      -> check e (t' (vfree (Name "_")))
  let res = fst (ann e')
  pure (In (Lam n e') (maybe id Resources.delete n res, VPi tn pi t t'))
elab tm (Just ty) = do
  v <- infer tm
  unless (snd (ann v) == ty) (throwError (TypeMismatch ty (snd (ann v)) (ann tm)))
  pure v

infer :: ( Carrier sig m
         , Member (Error ElabError) sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Surface Name) Span
      -> m (Term (Core Name) (Resources Usage, Type))
infer tm = elab tm Nothing

check :: ( Carrier sig m
         , Member (Error ElabError) sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Surface Name) Span
      -> Type
      -> m (Term (Core Name) (Resources Usage, Type))
check tm = elab tm . Just


type ModuleTable = Map.Map ModuleName (Context, Env)

elabModule :: (Carrier sig m, Effect sig, Member (Error ElabError) sig, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig) => Module (Term (Surface Name) Span) -> m (Context, Env)
elabModule (Module _ imports decls) = runState Context.empty . execState (mempty :: Env) $ do
  for_ imports $ \ (Import name) -> do
    (ctx, env) <- importModule name
    modify (Context.union ctx)
    modify (<> env)

  for_ decls $ \case
    Declare name ty -> elabDecl name ty
    Define  name tm -> elabDef  name tm

importModule :: (Carrier sig m, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig, Monad m) => ModuleName -> m (Context, Env)
importModule n = asks (Map.lookup n) >>= maybe (throwError (UnknownModule n)) pure


elabDecl :: (Carrier sig m, Member (Error ElabError) sig, Member (State Context) sig, Member (State Env) sig, Monad m) => String -> Term (Surface Name) Span -> m ()
elabDecl name ty = do
  ty' <- runInState Zero (check ty VType)
  ty'' <- gets (eval ty')
  modify (Context.insert (Name name) ty'')

elabDef :: (Carrier sig m, Member (Error ElabError) sig, Member (State Context) sig, Member (State Env) sig, Monad m) => String -> Term (Surface Name) Span -> m ()
elabDef name tm = do
  ty <- gets (Context.lookup (Name name))
  tm' <- runInState One (maybe infer (flip check) ty tm)
  tm'' <- gets (eval tm')
  modify (Map.insert name tm'')
  maybe (modify (Context.insert (Name name) (snd (ann tm')))) (const (pure ())) ty

runInState :: (Carrier sig m, Member (State Context) sig, Member (State Env) sig, Monad m) => Usage -> Eff (ReaderC Context (Eff (ReaderC Env (Eff (ReaderC Usage m))))) a -> m a
runInState usage m = do
  env <- get
  ctx <- get
  runReader usage (runReader env (runReader ctx m))


data ElabError
  = FreeVariable Name Span
  | TypeMismatch Type Type Span
  | NoRuleToInfer (Term (Surface Name) Span) Span
  | IllegalApplication (Term (Core Name) (Resources Usage, Type)) Span
  | ResourceMismatch String Usage Usage Span [Span]
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (FreeVariable name span) = nest 2 $ pretty "free variable " <+> squotes (pretty name) <$$> pretty (render span)
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

instance PrettyPrec ElabError

runElabError :: (Carrier sig m, Effect sig, Monad m) => Eff (ErrorC ElabError m) a -> m (Either ElabError a)
runElabError = runError
