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
        )
     => Term (Surface QName) Span
     -> Maybe (Type QName)
     -> Elab QName m (Term (Core QName) (Resources QName Usage, Type QName))
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
    _ -> throwError (IllegalApplication (() <$ f') (snd (ann f')) (ann f))
elab tm Nothing = throwError (NoRuleToInfer tm (ann tm))
elab (In (Surface.Lam n e) span) (Just (VPi tn pi t t')) = do
  e' <- local (Context.insert n t) (check (subst n (Surface.Var n) e) (t' (vfree n)))
  let res = fst (ann e')
      used = Resources.lookup n res
  sigma <- ask
  unless (sigma >< pi == More) . when (pi /= used) $
    throwError (ResourceMismatch n pi used span (uses n e))
  pure (In (Core.Lam n e') (Resources.delete n res, VPi tn pi t t'))
elab (In (Surface.Hole n) span) (Just ty) = do
  ctx <- ask
  throwError (TypedHole n ty (Context.filter (const . isLocal) ctx) span)
elab tm (Just ty) = do
  v <- infer tm
  actual <- asks (flip vforce (snd (ann v)))
  unless (actual == ty) (throwError (TypeMismatch ty (snd (ann v)) (ann tm)))
  pure v

infer :: ( Carrier sig m
         , Member (Error (ElabError QName)) sig
         , Member (Reader (Context QName)) sig
         , Member (Reader (Env QName)) sig
         , Member (Reader Usage) sig
         )
      => Term (Surface QName) Span
      -> Elab QName m (Term (Core QName) (Resources QName Usage, Type QName))
infer tm = elab tm Nothing

check :: ( Carrier sig m
         , Member (Error (ElabError QName)) sig
         , Member (Reader (Context QName)) sig
         , Member (Reader (Env QName)) sig
         , Member (Reader Usage) sig
         )
      => Term (Surface QName) Span
      -> Type QName
      -> Elab QName m (Term (Core QName) (Resources QName Usage, Type QName))
check tm ty = asks (flip vforce ty) >>= elab tm . Just


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


elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error (ElabError QName)) sig
              , Member (Error ModuleError) sig
              , Member (Reader (ModuleTable QName)) sig
              )
           => Module QName (Term (Surface QName) Span) Span
           -> Elab QName m (Context QName, Env QName)
elabModule m = raiseHandler (runState Context.empty . runElab . execState Env.empty) $ do
  for_ (moduleImports m) $ \ i -> do
    (ctx, env) <- importModule i
    modify (Context.union ctx)
    modify (Env.union env)

  for_ (moduleDecls m) $ \case
    Declare name ty -> elabDecl name ty
    Define  name tm -> elabDef  name tm

importModule :: ( Carrier sig m
                , Member (Error ModuleError) sig
                , Member (Reader (ModuleTable QName)) sig
                )
             => Import Span
             -> Elab QName m (Context QName, Env QName)
importModule n = do
  (ctx, env) <- asks (Map.lookup (importModuleName n)) >>= maybe (throwError (UnknownModule n)) pure
  pure (Context.filter p ctx, Env.filter p env)
  where p = const . inModule (importModuleName n)


elabDecl :: ( Carrier sig m
            , Member (Error (ElabError QName)) sig
            , Member (State (Context QName)) sig
            , Member (State (Env QName)) sig
            )
         => QName
         -> Term (Surface QName) Span
         -> Elab QName m ()
elabDecl name ty = do
  ty' <- runInState Zero (check ty VType)
  ty'' <- gets (eval ty')
  modify (Context.insert name ty'')

elabDef :: ( Carrier sig m
           , Member (Error (ElabError QName)) sig
           , Member (State (Context QName)) sig
           , Member (State (Env QName)) sig
           )
        => QName
        -> Term (Surface QName) Span
        -> Elab QName m ()
elabDef name tm = do
  ty <- gets (Context.lookup name)
  tm' <- runInState One (maybe infer (flip check) ty tm)
  tm'' <- gets (eval tm')
  modify (Env.insert name tm'')
  maybe (modify (Context.insert name (snd (ann tm')))) (const (pure ())) ty

runInState :: ( Carrier sig m
              , Member (State (Context v)) sig
              , Member (State (Env v)) sig
              )
           => Usage
           -> Elab v (ReaderC (Context v) (Eff
                     (ReaderC (Env v)     (Eff
                     (ReaderC Usage       (Eff m)))))) a
           -> Elab v m a
runInState usage m = do
  env <- get
  ctx <- get
  raiseHandler (runReader usage . runReader env . runReader ctx) m


data ElabError v
  = FreeVariable v Span
  | TypeMismatch (Type v) (Type v) Span
  | NoRuleToInfer (Term (Surface v) Span) Span
  | IllegalApplication (Term (Core v) ()) (Type v) Span
  | ResourceMismatch v Usage Usage Span [Span]
  | TypedHole v (Type v) (Context v) Span
  deriving (Eq, Ord, Show)

instance (Ord v, Pretty v) => Pretty (ElabError v) where
  pretty (FreeVariable name span) = prettyErr span (pretty "free variable" <+> squotes (pretty name)) Nothing
  pretty (TypeMismatch expected actual span) = prettyErr span (vsep
    [ pretty "type mismatch"
    , pretty "expected:" <+> pretty expected
    , pretty "  actual:" <+> pretty actual
    ]) Nothing
  pretty (NoRuleToInfer _ span) = prettyErr span (pretty "no rule to infer type of term") Nothing
  pretty (IllegalApplication tm ty span) = prettyErr span (pretty "illegal application of non-function term" <+> pretty tm <+> colon <+> pretty ty) Nothing
  pretty (ResourceMismatch n pi used span spans) = prettyErr span msg (if length spans == 0 then Nothing else Just (vsep (map prettys spans)))
    where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length spans)) <+> pretty "than required" <+> parens (pretty pi)
  pretty (TypedHole n ty ctx span) = prettyErr span msg (Just ext)
    where msg = pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
          ext = nest 2 $ vsep
            [ pretty "Local bindings:"
            , pretty ctx
            ]

instance (Ord v, Pretty v) => PrettyPrec (ElabError v)
