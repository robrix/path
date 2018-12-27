{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect hiding ((:+:))
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
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
import Path.Term
import Path.Usage
import Path.Value as Value
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import Text.Trifecta.Rendering (Span)

elab :: ( Carrier sig m
        , Member (Error ElabError) sig
        , Member Fresh sig
        , Member (Reader Context) sig
        , Member (Reader Env) sig
        , Member (Reader Usage) sig
        , Monad m
        )
     => Term (Implicit QName :+: Core Name QName) Span
     -> Maybe (Type QName)
     -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
elab (In out span) ty = case (out, ty) of
  (R Core.Type, Nothing) -> pure (In Core.Type (Resources.empty, Value.Type))
  (R (Core.Pi n e t b), Nothing) -> do
    t' <- check t Value.Type
    t'' <- eval t'
    b' <- local (Context.insert (Local n) t'') (check b Value.Type)
    pure (In (Core.Pi n e t' b') (Resources.empty, Value.Type))
  (R (Var n), Nothing) -> do
    res <- asks (Context.lookup n)
    sigma <- ask
    case res of
      Just t -> pure (In (Core.Var n) (Resources.singleton n sigma, t))
      _      -> throwError (FreeVariable n span)
  (R (f :@ a), Nothing) -> do
    f' <- infer f
    case ann f' of
      (g1, Value.Pi n pi t t') -> do
        a' <- check a t
        let (g2, _) = ann a'
        a'' <- eval a'
        pure (In (f' Core.:@ a') (g1 <> pi ><< g2, subst (Local n) a'' t'))
      _ -> throwError (IllegalApplication (() <$ f') (snd (ann f')) (ann f))
  (_, Nothing) -> ask >>= \ ctx -> throwError (NoRuleToInfer (Context.filter (const . isLocal) ctx) span)
  (R (Core.Lam n e), Just (Value.Pi tn pi t t')) -> do
    e' <- local (Context.insert (Local n) t) (check e (subst (Local tn) (vfree (Local n)) t'))
    let res = fst (ann e')
        used = Resources.lookup (Local n) res
    sigma <- ask
    unless (sigma >< pi == More) . when (pi /= used) $
      throwError (ResourceMismatch n pi used span (uses n e))
    pure (In (Core.Lam n e') (Resources.delete (Local n) res, Value.Pi tn pi t t'))
  (L (Hole n), Just ty) -> do
    ctx <- ask
    throwError (TypedHole n ty (Context.filter (const . isLocal) ctx) span)
  (tm, Just ty) -> do
    v <- infer (In tm span)
    actual <- vforce (snd (ann v))
    unless (actual `aeq` ty) (throwError (TypeMismatch ty (snd (ann v)) span))
    pure v

infer :: ( Carrier sig m
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
infer tm = elab tm Nothing

check :: ( Carrier sig m
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Implicit QName :+: Core Name QName) Span
      -> Type QName
      -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
check tm ty = vforce ty >>= elab tm . Just


type ModuleTable = Map.Map ModuleName (Context, Env)

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error ModuleError) sig
              , Member Fresh sig
              , Member (Reader ModuleTable) sig
              , Member (State [ElabError]) sig
              )
           => Module QName (Term (Implicit QName :+: Core Name QName) Span)
           -> m (Context, Env)
elabModule m = runState Context.empty . execState Env.empty $ do
  for_ (moduleImports m) $ \ i -> do
    (ctx, env) <- importModule i
    modify (Context.union ctx)
    modify (Env.union env)

  for_ (moduleDecls m) (either ((Nothing <$) . logError) (pure . Just) <=< runError . elabDecl)

logError :: (Carrier sig m, Member (State [ElabError]) sig, Monad m) => ElabError -> m ()
logError = modify . (:)

importModule :: ( Carrier sig m
                , Member (Error ModuleError) sig
                , Member (Reader ModuleTable) sig
                , Monad m
                )
             => Import
             -> m (Context, Env)
importModule n = do
  (ctx, env) <- asks (Map.lookup (importModuleName n)) >>= maybe (throwError (UnknownModule n)) pure
  pure (Context.filter p ctx, Env.filter p env)
  where p = const . inModule (importModuleName n)


elabDecl :: ( Carrier sig m
            , Member (Error ElabError) sig
            , Member Fresh sig
            , Member (State Context) sig
            , Member (State Env) sig
            , Monad m
            )
         => Decl QName (Term (Implicit QName :+: Core Name QName) Span)
         -> m (Decl QName (Term (Core Name QName) (Resources QName Usage, Type QName)))
elabDecl = \case
  Declare name ty -> Declare name <$> elabDeclare name ty
  Define  name tm -> Define  name <$> elabDefine  name tm
  Doc docs     d  -> Doc docs <$> elabDecl d

elabDeclare :: ( Carrier sig m
               , Member (Error ElabError) sig
               , Member Fresh sig
               , Member (State Context) sig
               , Member (State Env) sig
               , Monad m
               )
            => QName
            -> Term (Implicit QName :+: Core Name QName) Span
            -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
elabDeclare name ty = do
  ty' <- runReader Zero (runContext (runEnv (check ty Value.Type)))
  ty'' <- runEnv (eval ty')
  ty' <$ modify (Context.insert name ty'')

elabDefine :: ( Carrier sig m
              , Member (Error ElabError) sig
              , Member Fresh sig
              , Member (State Context) sig
              , Member (State Env) sig
              , Monad m
              )
           => QName
           -> Term (Implicit QName :+: Core Name QName) Span
           -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
elabDefine name tm = do
  ty <- gets (Context.lookup name)
  tm' <- runReader One (runContext (runEnv (maybe infer (flip check) ty tm)))
  tm'' <- runEnv (eval tm')
  modify (Env.insert name tm'')
  tm' <$ maybe (modify (Context.insert name (snd (ann tm')))) (const (pure ())) ty

runContext :: (Carrier sig m, Member (State Context) sig, Monad m) => Eff (ReaderC Context m) a -> m a
runContext m = get >>= flip runReader m

runEnv :: (Carrier sig m, Member (State Env) sig, Monad m) => Eff (ReaderC Env m) a -> m a
runEnv m = get >>= flip runReader m


data ElabError
  = FreeVariable QName Span
  | TypeMismatch (Type QName) (Type QName) Span
  | NoRuleToInfer Context Span
  | IllegalApplication (Term (Core Name QName) ()) (Type QName) Span
  | ResourceMismatch Name Usage Usage Span [Span]
  | TypedHole QName (Type QName) Context Span
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty = \case
    FreeVariable name span -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) Nothing
    TypeMismatch expected actual span -> prettyErr span (vsep
      [ pretty "type mismatch"
      , pretty "expected:" <+> pretty expected
      , pretty "  actual:" <+> pretty actual
      ]) Nothing
    NoRuleToInfer ctx span -> prettyErr span (pretty "no rule to infer type of term") (Just (prettyCtx ctx))
    IllegalApplication tm ty span -> prettyErr span (pretty "illegal application of non-function term" <+> pretty tm <+> colon <+> pretty ty) Nothing
    ResourceMismatch n pi used span spans -> prettyErr span msg (vsep (map prettys spans) <$ listToMaybe spans)
      where msg = pretty "Variable" <+> squotes (pretty n) <+> pretty "used" <+> pretty (if pi > used then "less" else "more") <+> parens (pretty (length spans)) <+> pretty "than required" <+> parens (pretty pi)
    TypedHole n ty ctx span -> prettyErr span msg (Just (prettyCtx ctx))
      where msg = pretty "Found hole" <+> squotes (pretty n) <+> pretty "of type" <+> squotes (pretty ty)
    where prettyCtx ctx = nest 2 $ vsep
            [ pretty "Local bindings:"
            , pretty ctx
            ]

instance PrettyPrec ElabError
