{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad (unless, when)
import Control.Monad.IO.Class
import Data.Coerce (coerce)
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
        , Ord v
        , Show v
        )
     => Term (Surface v) Span
     -> Maybe (Type v)
     -> Elab v m (Term (Core v) (Resources v Usage, Type v))
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
elab (In (Surface.Hole n) span) (Just ty) = throwError (TypedHole n ty span)
elab tm (Just ty) = do
  v <- infer tm
  unless (snd (ann v) == ty) (throwError (TypeMismatch ty (snd (ann v)) (ann tm)))
  pure v

infer :: ( Carrier sig m
         , Member (Error (ElabError v)) sig
         , Member (Reader (Context v)) sig
         , Member (Reader (Env v)) sig
         , Member (Reader Usage) sig
         , Ord v
         , Show v
         )
      => Term (Surface v) Span
      -> Elab v m (Term (Core v) (Resources v Usage, Type v))
infer tm = elab tm Nothing

check :: ( Carrier sig m
         , Member (Error (ElabError v)) sig
         , Member (Reader (Context v)) sig
         , Member (Reader (Env v)) sig
         , Member (Reader Usage) sig
         , Ord v
         , Show v
         )
      => Term (Surface v) Span
      -> Type v
      -> Elab v m (Term (Core v) (Resources v Usage, Type v))
check tm = elab tm . Just


type ModuleTable v = Map.Map ModuleName (Context v, Env v)

newtype Elab v m a = Elab { runElab :: Eff m a }
  deriving (Applicative, Functor, Monad)

deriving instance (Carrier sig m, Member (Lift IO) sig) => MonadIO (Elab v m)

instance Carrier sig m => Carrier sig (Elab v m) where
  ret = Elab . ret
  eff = Elab . eff . handlePure runElab

raiseHandler :: (Eff m a -> Eff n b)
             -> Elab v m a
             -> Elab v n b
raiseHandler = coerce


elabModule :: (Carrier sig m, Effect sig, Member (Error (ElabError QName)) sig, Member (Error ModuleError) sig, Member (Reader (ModuleTable QName)) sig) => Module QName (Term (Surface QName) Span) -> Elab QName m (Context QName, Env QName)
elabModule m = raiseHandler (runState Context.empty . runElab . execState Env.empty) $ do
  for_ (moduleImports m) $ \ (Import name) -> do
    (ctx, env) <- importModule name
    modify (Context.union ctx)
    modify (Env.union env)

  for_ (moduleDecls m) $ \case
    Declare name ty -> elabDecl name ty
    Define  name tm -> elabDef  name tm

importModule :: (Carrier sig m, Member (Error ModuleError) sig, Member (Reader (ModuleTable QName)) sig) => ModuleName -> Elab QName m (Context QName, Env QName)
importModule n = do
  (ctx, env) <- asks (Map.lookup n) >>= maybe (throwError (UnknownModule n)) pure
  pure (Context.filter (const . inModule n) ctx, Env.filter (const . inModule n) env)
  where inModule m (m' :.: _) = m == m'
        inModule _ _          = False


elabDecl :: (Carrier sig m, Member (Error (ElabError v)) sig, Member (State (Context v)) sig, Member (State (Env v)) sig, Ord v, Show v) => v -> Term (Surface v) Span -> Elab v m ()
elabDecl name ty = do
  ty' <- runInState Zero (check ty VType)
  ty'' <- gets (eval ty')
  modify (Context.insert name ty'')

elabDef :: (Carrier sig m, Member (Error (ElabError v)) sig, Member (State (Context v)) sig, Member (State (Env v)) sig, Ord v, Show v) => v -> Term (Surface v) Span -> Elab v m ()
elabDef name tm = do
  ty <- gets (Context.lookup name)
  tm' <- runInState One (maybe infer (flip check) ty tm)
  tm'' <- gets (eval tm')
  modify (Env.insert name tm'')
  maybe (modify (Context.insert name (snd (ann tm')))) (const (pure ())) ty

runInState :: (Carrier sig m, Member (State (Context v)) sig, Member (State (Env v)) sig) => Usage -> Elab v (ReaderC (Context v) (Eff (ReaderC (Env v) (Eff (ReaderC Usage (Eff m)))))) a -> Elab v m a
runInState usage m = do
  env <- get
  ctx <- get
  raiseHandler (runReader usage . runReader env . runReader ctx) m


data ElabError v
  = FreeVariable v Span
  | TypeMismatch (Type v) (Type v) Span
  | NoRuleToInfer (Term (Surface v) Span) Span
  | IllegalApplication (Term (Core v) (Resources v Usage, Type v)) Span
  | ResourceMismatch v Usage Usage Span [Span]
  | TypedHole v (Type v) Span
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
  pretty (TypedHole n ty span) = nest 2 $ vsep
    [ pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
    , pretty (render span)
    ]

instance (Ord v, Pretty v) => PrettyPrec (ElabError v)
