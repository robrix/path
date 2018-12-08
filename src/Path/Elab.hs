{-# LANGUAGE FlexibleContexts #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Control.Monad ((<=<), unless)
import Data.Foldable (for_, traverse_)
import qualified Data.Map as Map
import Path.Context as Context
import Path.Core
import Path.Decl
import Path.Eval
import Path.Module
import Path.Name
import Path.Semiring
import Path.Surface
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen
import Text.Trifecta.Rendering (Span, render)

elab :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Member (Reader Env) sig, Member (Reader Usage) sig, Monad m) => Term (Ann Surface Span) -> Maybe Type -> m (Term (Ann Core Type))
elab (In (Ann (e ::: t) _)) Nothing = do
  t' <- check t VType
  t'' <- asks (eval (erase t'))
  check e t''
elab (In (Ann (Core Type) _)) Nothing = pure (In (Ann Type VType))
elab (In (Ann (Core (Pi n e t b)) _)) Nothing = do
  t' <- check t VType
  t'' <- asks (eval (erase t'))
  b' <- local (Context.insert (Local n) (Zero, t'')) (check (subst n (Core (Var (Local n))) b) VType)
  pure (In (Ann (Pi n e t' b') VType))
elab (In (Ann (Core (Var n)) span)) Nothing = do
  res <- asks (Context.disambiguate <=< Context.lookup n)
  sigma <- ask
  case res of
    Just (usage, t)
      | usage == sigma -> pure (In (Ann (Var n) t))
    _                  -> throwError (FreeVariable n span)
elab (In (Ann (Core (f :@ a)) _)) Nothing = do
  f' <- infer f
  case ann (out f') of
    VPi _ _ t t' -> do
      a' <- check a t
      env <- ask
      pure (In (Ann (f' :@ a') (t' (eval (erase a') env))))
    _ -> throwError (IllegalApplication f' (ann (out f)))
elab tm Nothing = throwError (NoRuleToInfer tm (ann (out tm)))
elab (In (Ann (Core (Lam n e)) _)) (Just (VPi tn pi t t')) = do
  sigma <- ask
  e' <- local (Context.insert (Local n) (sigma >< pi, t)) (check (subst n (Core (Var (Local n))) e) (t' (vfree (Local n))))
  pure (In (Ann (Lam n e') (VPi tn pi t t')))
elab tm (Just ty) = do
  v <- infer tm
  unless (ann (out v) == ty) (throwError (TypeMismatch ty (ann (out v)) (ann (out tm))))
  pure v

infer :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Member (Reader Env) sig, Member (Reader Usage) sig, Monad m) => Term (Ann Surface Span) -> m (Term (Ann Core Type))
infer tm = elab tm Nothing

check :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Member (Reader Env) sig, Member (Reader Usage) sig, Monad m) => Term (Ann Surface Span) -> Type -> m (Term (Ann Core Type))
check tm = elab tm . Just


type ModuleTable = Map.Map ModuleName (Context, Env)

elabModule :: (Carrier sig m, Effect sig, Member (Error ElabError) sig, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig) => Module (Term (Ann Surface Span)) -> m (Context, Env)
elabModule (Module _ imports decls) = runState Context.empty . execState (mempty :: Env) $ do
  for_ imports $ \ (Import name) -> do
    (ctx, env) <- importModule name
    modify (Context.union ctx)
    modify (<> env)

  traverse_ elabDecl decls

importModule :: (Carrier sig m, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig, Monad m) => ModuleName -> m (Context, Env)
importModule n = asks (Map.lookup n) >>= maybe (throwError (UnknownModule n)) pure


elabDecl :: (Carrier sig m, Member (Error ElabError) sig, Member (State Context) sig, Member (State Env) sig, Monad m) => Decl (Term (Ann Surface Span)) -> m ()
elabDecl (Declare name ty) = do
  ty' <- runInState Zero (check ty VType)
  ty'' <- gets (eval (erase ty'))
  modify (Context.insert (Global name) (Zero, ty''))
elabDecl (Define name usage tm) = do
  ty <- gets (Context.disambiguate <=< Context.lookup (Global name))
  tm' <- runInState usage (maybe infer (flip check . snd) ty tm)
  tm'' <- gets (eval (erase tm'))
  modify (Map.insert name tm'')
  maybe (modify (Context.insert (Global name) (Zero, ann (out tm')))) (const (pure ())) ty

runInState :: (Carrier sig m, Member (State Context) sig, Member (State Env) sig, Monad m) => Usage -> Eff (ReaderC Context (Eff (ReaderC Env (Eff (ReaderC Usage m))))) a -> m a
runInState usage m = do
  env <- get
  ctx <- get
  runReader usage (runReader env (runReader ctx m))


data ElabError
  = FreeVariable Name Span
  | TypeMismatch Type Type Span
  | NoRuleToInfer (Term (Ann Surface Span)) Span
  | IllegalApplication (Term (Ann Core Type)) Span
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (FreeVariable name span) = nest 2 $ pretty "free variable " <+> squotes (pretty name) <$$> pretty (render span)
  pretty (TypeMismatch expected actual span) = nest 2 $ vsep [ pretty "type mismatch", pretty "expected:" <+> pretty expected, pretty "  actual:" <+> pretty actual, pretty (render span) ]
  pretty (NoRuleToInfer _ span) = pretty "no rule to infer type of term" <$$> pretty (render span)
  pretty (IllegalApplication tm span) = pretty "illegal application of non-function term" <+> pretty tm <$$> pretty (render span)

runElabError :: (Carrier sig m, Effect sig, Monad m) => Eff (ErrorC ElabError m) a -> m (Either ElabError a)
runElabError = runError
