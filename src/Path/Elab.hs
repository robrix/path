{-# LANGUAGE FlexibleContexts #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Control.Monad (unless)
import Data.Foldable (for_, traverse_)
import qualified Data.Map as Map
import Data.Text.Prettyprint.Doc
import Path.Core
import Path.Decl
import Path.Eval
import Path.Module
import Path.Name
import Path.Surface
import Path.Term

type Type = Value

type Context = Map.Map Name Value

elab :: (Carrier sig m, Member (Error Err) sig, Member (Reader Context) sig, Member (Reader Env) sig, Monad m) => Term Surface -> Maybe Type -> m (Term (Ann Core Type))
elab (In (e ::: t)) Nothing = do
  t' <- check t VType
  t'' <- asks (eval (erase t'))
  check e t''
elab (In (Core Type)) Nothing = pure (In (Ann Type VType))
elab (In (Core (Pi n e t b))) Nothing = do
  t' <- check t VType
  t'' <- asks (eval (erase t'))
  b' <- local (Map.insert (Local n) t'') (check (subst n (In (Core (Free (Local n)))) b) VType)
  pure (In (Ann (Pi n e t' b') VType))
elab (In (Core (Free n))) Nothing = asks (Map.lookup n) >>= maybe (throwError (FreeVariable n)) (pure . In . Ann (Free n))
elab (In (Core (f :@ a))) Nothing = do
  f' <- infer f
  case ann (out f') of
    VPi _ _ t t' -> do
      a' <- check a t
      env <- ask
      pure (In (Ann (f' :@ a') (t' (eval (erase a') env))))
    _ -> throwError (IllegalApplication f')
elab tm Nothing = throwError (NoRuleToInfer tm)
elab (In (Core (Lam n e))) (Just (VPi tn ann t t')) = do
  e' <- local (Map.insert (Local n) t) (check (subst n (In (Core (Free (Local n)))) e) (t' (vfree (Local n))))
  pure (In (Ann (Lam n e') (VPi tn ann t t')))
elab tm (Just ty) = do
  v <- infer tm
  unless (ann (out v) == ty) (throwError (TypeMismatch ty (ann (out v))))
  pure v

infer :: (Carrier sig m, Member (Error Err) sig, Member (Reader Context) sig, Member (Reader Env) sig, Monad m) => Term Surface -> m (Term (Ann Core Type))
infer tm = elab tm Nothing

check :: (Carrier sig m, Member (Error Err) sig, Member (Reader Context) sig, Member (Reader Env) sig, Monad m) => Term Surface -> Type -> m (Term (Ann Core Type))
check tm = elab tm . Just


type ModuleTable = Map.Map ModuleName (Context, Env)

elabModule :: (Carrier sig m, Member (Error Err) sig, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig, Member (State Context) sig, Member (State Env) sig, Monad m) => Module -> m ()
elabModule (Module _ imports decls) = transactionState $ do
  for_ imports $ \ (Import name) -> do
    (ctx, env) <- importModule name
    modify (<> ctx)
    modify (<> env)

  traverse_ elabDecl decls

importModule :: (Carrier sig m, Member (Error ModuleError) sig, Member (Reader ModuleTable) sig, Monad m) => ModuleName -> m (Context, Env)
importModule n = asks (Map.lookup n) >>= maybe (throwError (UnknownModule n)) pure


elabDecl :: (Carrier sig m, Member (Error Err) sig, Member (State Context) sig, Member (State Env) sig, Monad m) => Decl -> m ()
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

transactionState :: (Carrier sig m, Member (Error Err) sig, Member (State Context) sig, Member (State Env) sig, Monad m) => m a -> m a
transactionState m = do
  env <- get
  ctx <- get
  m `catchError` \ err -> do
    put (env :: Env)
    put (ctx :: Context)
    throwError (err :: Err)


data Err
  = FreeVariable Name
  | TypeMismatch Type Type
  | NoRuleToInfer (Term Surface)
  | IllegalApplication (Term (Ann Core Type))
  deriving (Eq, Ord, Show)

instance Pretty Err where
  pretty (FreeVariable name) = pretty "free variable:" <+> pretty name
  pretty (TypeMismatch expected actual) = vsep [ pretty "expected:" <+> pretty expected, pretty "  actual:" <+> pretty actual ]
  pretty (NoRuleToInfer tm) = pretty "no rule to infer type of term:" <+> pretty tm
  pretty (IllegalApplication tm) = pretty "illegal application of term:" <+> pretty tm

prettyErr :: Err -> Doc ann
prettyErr = pretty
