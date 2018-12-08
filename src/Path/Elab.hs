{-# LANGUAGE FlexibleContexts #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Control.Monad (unless)
import Data.Foldable (for_, traverse_)
import qualified Data.Map as Map
import Path.Core
import Path.Decl
import Path.Eval
import Path.Module
import Path.Name
import Path.Surface
import Path.Term
import Text.PrettyPrint.ANSI.Leijen
import Text.Trifecta.Rendering (Span)

type Type = Value

type Context = Map.Map Name Value

elab :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Member (Reader Env) sig, Monad m) => Term (Ann Surface Span) -> Maybe Type -> m (Term (Ann Core Type))
elab (In (Ann (e ::: t) _)) Nothing = do
  t' <- check t VType
  t'' <- asks (eval (erase t'))
  check e t''
elab (In (Ann (Core Type) _)) Nothing = pure (In (Ann Type VType))
elab (In (Ann (Core (Pi n e t b)) _)) Nothing = do
  t' <- check t VType
  t'' <- asks (eval (erase t'))
  b' <- local (Map.insert (Local n) t'') (check (subst n (Core (Free (Local n))) b) VType)
  pure (In (Ann (Pi n e t' b') VType))
elab (In (Ann (Core (Free n)) _)) Nothing = asks (Map.lookup n) >>= maybe (throwError (FreeVariable n)) (pure . In . Ann (Free n))
elab (In (Ann (Core (f :@ a)) _)) Nothing = do
  f' <- infer f
  case ann (out f') of
    VPi _ _ t t' -> do
      a' <- check a t
      env <- ask
      pure (In (Ann (f' :@ a') (t' (eval (erase a') env))))
    _ -> throwError (IllegalApplication f')
elab tm Nothing = throwError (NoRuleToInfer tm)
elab (In (Ann (Core (Lam n e)) _)) (Just (VPi tn p t t')) = do
  e' <- local (Map.insert (Local n) t) (check (subst n (Core (Free (Local n))) e) (t' (vfree (Local n))))
  pure (In (Ann (Lam n e') (VPi tn p t t')))
elab tm (Just ty) = do
  v <- infer tm
  unless (ann (out v) == ty) (throwError (TypeMismatch ty (ann (out v))))
  pure v

infer :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Member (Reader Env) sig, Monad m) => Term (Ann Surface Span) -> m (Term (Ann Core Type))
infer tm = elab tm Nothing

check :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Member (Reader Env) sig, Monad m) => Term (Ann Surface Span) -> Type -> m (Term (Ann Core Type))
check tm = elab tm . Just


type ModuleTable = Map.Map ModuleName (Context, Env)

elabModule :: (Carrier sig m, Effect sig, Member (Error ElabError) sig, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig) => Module (Term (Ann Surface Span)) -> m (Context, Env)
elabModule (Module _ imports decls) = runState (mempty :: Context) . execState (mempty :: Env) $ do
  for_ imports $ \ (Import name) -> do
    (ctx, env) <- importModule name
    modify (<> ctx)
    modify (<> env)

  traverse_ elabDecl decls

importModule :: (Carrier sig m, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig, Monad m) => ModuleName -> m (Context, Env)
importModule n = asks (Map.lookup n) >>= maybe (throwError (UnknownModule n)) pure


elabDecl :: (Carrier sig m, Member (Error ElabError) sig, Member (State Context) sig, Member (State Env) sig, Monad m) => Decl (Term (Ann Surface Span)) -> m ()
elabDecl (Declare name ty) = do
  ty' <- runInState (check ty VType)
  ty'' <- gets (eval (erase ty'))
  modify (Map.insert (Global name) ty'')
elabDecl (Define name tm) = do
  ty <- gets (Map.lookup (Global name))
  tm' <- runInState (maybe infer (flip check) ty tm)
  tm'' <- gets (eval (erase tm'))
  modify (Map.insert name tm'')
  maybe (modify (Map.insert (Global name) (ann (out tm')))) (const (pure ())) ty

runInState :: (Carrier sig m, Member (State Context) sig, Member (State Env) sig, Monad m) => Eff (ReaderC Context (Eff (ReaderC Env m))) a -> m a
runInState m = do
  env <- get
  ctx <- get
  runReader env (runReader ctx m)


data ElabError
  = FreeVariable Name
  | TypeMismatch Type Type
  | NoRuleToInfer (Term (Ann Surface Span))
  | IllegalApplication (Term (Ann Core Type))
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (FreeVariable name) = pretty "free variable:" <+> pretty name
  pretty (TypeMismatch expected actual) = vsep [ pretty "expected:" <+> pretty expected, pretty "  actual:" <+> pretty actual ]
  pretty (NoRuleToInfer tm) = pretty "no rule to infer type of term:" <+> pretty tm
  pretty (IllegalApplication tm) = pretty "illegal application of term:" <+> pretty tm

runElabError :: (Carrier sig m, Effect sig, Monad m) => Eff (ErrorC ElabError m) a -> m (Either ElabError a)
runElabError = runError
