{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad ((<=<), unless, when)
import Data.Foldable (for_)
import qualified Data.Map as Map
import Data.Maybe (listToMaybe)
import Path.Context as Context
import Path.Core as Core
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
import Text.Trifecta.Rendering (Span)

elab :: ( Carrier sig m
        , Member (Error (ElabError QName)) sig
        , Member (Reader (Context QName)) sig
        , Member (Reader (Env QName)) sig
        , Member (Reader Usage) sig
        , Monad m
        )
     => Term (Surface QName) Span
     -> Maybe (Type QName)
     -> m (Term (Core QName) (Resources QName Usage, Type QName))
elab (In out span) ty = case (out, ty) of
  (e ::: t, Nothing) -> do
    t' <- check t VType
    t'' <- asks (flip eval t')
    check e t''
  (ForAll n t b, Nothing) -> do
    t' <- check t VType
    t'' <- asks (flip eval t')
    b' <- local (Context.insert n t'') (check (subst n (Surface.Var n) b) VType)
    pure (In (Core.Pi n Zero t' b') (Resources.empty, VType))
  (Surface.Type, Nothing) -> pure (In Core.Type (Resources.empty, VType))
  (Surface.Pi n e t b, Nothing) -> do
    t' <- check t VType
    t'' <- asks (flip eval t')
    b' <- local (Context.insert n t'') (check (subst n (Surface.Var n) b) VType)
    pure (In (Core.Pi n e t' b') (Resources.empty, VType))
  (Surface.Var n, Nothing) -> do
    res <- asks (Context.lookup n)
    sigma <- ask
    case res of
      Just t -> pure (In (Core.Var n) (Resources.singleton n sigma, t))
      _      -> throwError (FreeVariable n span)
  (f Surface.:@ a, Nothing) -> do
    f' <- infer f
    case ann f' of
      (g1, VPi _ pi t t') -> do
        a' <- check a t
        let (g2, _) = ann a'
        env <- ask
        pure (In (f' Core.:@ a') (g1 <> pi ><< g2, t' (eval env a')))
      _ -> throwError (IllegalApplication (() <$ f') (snd (ann f')) (ann f))
  (tm, Nothing) -> throwError (NoRuleToInfer (In tm span) span)
  (Surface.Lam n e, Just (VPi tn pi t t')) -> do
    e' <- local (Context.insert n t) (check (subst n (Surface.Var n) e) (t' (vfree n)))
    let res = fst (ann e')
        used = Resources.lookup n res
    sigma <- ask
    unless (sigma >< pi == More) . when (pi /= used) $
      throwError (ResourceMismatch n pi used span (uses n e))
    pure (In (Core.Lam n e') (Resources.delete n res, VPi tn pi t t'))
  (Surface.Hole n, Just ty) -> do
    ctx <- ask
    throwError (TypedHole n ty (Context.filter (const . isLocal) ctx) span)
  (tm, Just ty) -> do
    v <- infer (In tm span)
    actual <- asks (flip vforce (snd (ann v)))
    unless (actual == ty) (throwError (TypeMismatch ty (snd (ann v)) span))
    pure v

infer :: ( Carrier sig m
         , Member (Error (ElabError QName)) sig
         , Member (Reader (Context QName)) sig
         , Member (Reader (Env QName)) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Surface QName) Span
      -> m (Term (Core QName) (Resources QName Usage, Type QName))
infer tm = elab tm Nothing

check :: ( Carrier sig m
         , Member (Error (ElabError QName)) sig
         , Member (Reader (Context QName)) sig
         , Member (Reader (Env QName)) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Surface QName) Span
      -> Type QName
      -> m (Term (Core QName) (Resources QName Usage, Type QName))
check tm ty = asks (flip vforce ty) >>= elab tm . Just


type ModuleTable v = Map.Map ModuleName (Context v, Env v)

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error ModuleError) sig
              , Member (Reader (ModuleTable QName)) sig
              , Member (State [ElabError QName]) sig
              )
           => Module QName (Term (Surface QName) Span) Span
           -> m (Context QName, Env QName)
elabModule m = runState Context.empty . execState Env.empty $ do
  for_ (moduleImports m) $ \ i -> do
    (ctx, env) <- importModule i
    modify (Context.union ctx)
    modify (Env.union env)

  for_ (moduleDecls m) (either logError pure <=< runError . elabDecl)

logError :: (Carrier sig m, Member (State [ElabError QName]) sig, Monad m) => ElabError QName -> m ()
logError = modify . (:)

importModule :: ( Carrier sig m
                , Member (Error ModuleError) sig
                , Member (Reader (ModuleTable QName)) sig
                , Monad m
                )
             => Import Span
             -> m (Context QName, Env QName)
importModule n = do
  (ctx, env) <- asks (Map.lookup (importModuleName n)) >>= maybe (throwError (UnknownModule n)) pure
  pure (Context.filter p ctx, Env.filter p env)
  where p = const . inModule (importModuleName n)


elabDecl :: ( Carrier sig m
            , Member (Error (ElabError QName)) sig
            , Member (State (Context QName)) sig
            , Member (State (Env QName)) sig
            , Monad m
            )
         => Decl QName (Term (Surface QName) Span)
         -> m ()
elabDecl = \case
  Declare name ty -> elabDeclare name ty
  Define  name tm -> elabDefine  name tm
  Doc _        d  -> elabDecl d

elabDeclare :: ( Carrier sig m
               , Member (Error (ElabError QName)) sig
               , Member (State (Context QName)) sig
               , Member (State (Env QName)) sig
               , Monad m
               )
            => QName
            -> Term (Surface QName) Span
            -> m ()
elabDeclare name ty = do
  ty' <- runInState Zero (check ty VType)
  ty'' <- gets (flip eval ty')
  modify (Context.insert name ty'')

elabDefine :: ( Carrier sig m
              , Member (Error (ElabError QName)) sig
              , Member (State (Context QName)) sig
              , Member (State (Env QName)) sig
              , Monad m
              )
           => QName
           -> Term (Surface QName) Span
           -> m ()
elabDefine name tm = do
  ty <- gets (Context.lookup name)
  tm' <- runInState One (maybe infer (flip check) ty tm)
  tm'' <- gets (flip eval tm')
  modify (Env.insert name tm'')
  maybe (modify (Context.insert name (snd (ann tm')))) (const (pure ())) ty

runInState :: ( Carrier sig m
              , Member (State (Context QName)) sig
              , Member (State (Env QName)) sig
              , Monad m
              )
           => Usage
           -> Eff (ReaderC (Context QName) (Eff
                  (ReaderC (Env QName)     (Eff
                  (ReaderC Usage           m))))) a
           -> m a
runInState usage m = do
  env <- get
  ctx <- get
  runReader usage (runReader env (runReader ctx m))


data ElabError v
  = FreeVariable v Span
  | TypeMismatch (Type v) (Type v) Span
  | NoRuleToInfer (Term (Surface v) Span) Span
  | IllegalApplication (Term (Core v) ()) (Type v) Span
  | ResourceMismatch v Usage Usage Span [Span]
  | TypedHole v (Type v) (Context v) Span
  deriving (Eq, Ord, Show)

instance (Ord v, Pretty v) => Pretty (ElabError v) where
  pretty = \case
    FreeVariable name span -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) Nothing
    TypeMismatch expected actual span -> prettyErr span (vsep
      [ pretty "type mismatch"
      , pretty "expected:" <+> pretty expected
      , pretty "  actual:" <+> pretty actual
      ]) Nothing
    NoRuleToInfer _ span -> prettyErr span (pretty "no rule to infer type of term") Nothing
    IllegalApplication tm ty span -> prettyErr span (pretty "illegal application of non-function term" <+> pretty tm <+> colon <+> pretty ty) Nothing
    ResourceMismatch n pi used span spans -> prettyErr span msg (vsep (map prettys spans) <$ listToMaybe spans)
      where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length spans)) <+> pretty "than required" <+> parens (pretty pi)
    TypedHole n ty ctx span -> prettyErr span msg (Just ext)
      where msg = pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
            ext = nest 2 $ vsep
              [ pretty "Local bindings:"
              , pretty ctx
              ]

instance (Ord v, Pretty v) => PrettyPrec (ElabError v)
