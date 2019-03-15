{-# LANGUAGE FlexibleContexts, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Solver where

import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.State
import           Control.Effect.Writer
import           Control.Monad ((>=>), guard, unless, when)
import           Data.Foldable (fold, foldl', toList)
import           Data.List (intersperse)
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Path.Constraint
import           Path.Context as Context
import           Path.Error
import           Path.Eval
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Scope hiding (null)
import           Path.Stack
import           Path.Value as Value hiding (Scope (..))
import           Prelude hiding (pi)
import           Text.Trifecta.Rendering (Span(..), Spanned(..))

type Blocked = Map.Map Gensym (Set.Set HomConstraint)
type Substitution = Map.Map Gensym (Value Meta)
type Queue = Seq.Seq HomConstraint

simplify :: ( Carrier sig m
            , Effect sig
            , Member (Error ElabError) sig
            , Member Naming sig
            , Member (Reader Scope) sig
            )
         => Caused (Equation (Value Meta) ::: Type Meta)
         -> m (Set.Set (Caused (Equation (Value Meta) ::: Type Meta)))
simplify = execWriter . go
  where go = \case
          (tm1 :===: tm2) ::: _ :@ _ | tm1 == tm2 -> pure ()
          q@((Pi p1 u1 t1 b1 :===: Pi p2 u2 t2 b2) ::: Type) :@ cause
            | p1 == p2, u1 == u2 -> do
              (_, n) <- freshName
              go ((t1               :===: t2              ) ::: Type :@ Via q cause)
              go ((instantiate n b1 :===: instantiate n b2) ::: Type :@ Via q cause)
          q@((Pi Im _ _ b1 :===: t2) ::: Type) :@ cause -> do
            n <- exists
            go ((instantiate n b1 :===: t2) ::: Type :@ Via q cause)
          q@((t1 :===: Pi Im _ _ b2) ::: Type) :@ cause -> do
            n <- exists
            go ((t1 :===: instantiate n b2) ::: Type :@ Via q cause)
          q@((Lam b1 :===: Lam b2) ::: Pi _ _ t b) :@ cause -> do
            (_, n) <- freshName
            go ((instantiate n b1 :===: instantiate n b2) ::: instantiate t b :@ Via q cause)
          q@((f1@(Qual (_ :.: _)) :$ sp1 :===: f2@(Qual (_ :.: _)) :$ sp2) ::: ty) :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            t2 <- whnf (f2 :$ sp2)
            go ((t1 :===: t2) ::: ty :@ Via q cause)
          q@((f1@(Qual (_ :.: _)) :$ sp1 :===: t2) ::: ty) :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            go ((t1 :===: t2) ::: ty :@ Via q cause)
          q@((t1 :===: f2@(Qual (_ :.: _)) :$ sp2) ::: ty) :@ cause -> do
            t2 <- whnf (f2 :$ sp2)
            go ((t1 :===: t2) ::: ty :@ Via q cause)
          q@((tm1 :===: Lam b2) ::: ty) :@ cause -> do
            (n, v) <- freshName
            go ((lam n (tm1 $$ v) :===: Lam b2) ::: ty :@ Via q cause)
          q@((Lam b1 :===: tm2) ::: ty) :@ cause -> do
            (n, v) <- freshName
            go ((Lam b1 :===: lam n (tm2 $$ v)) ::: ty :@ Via q cause)
          q@((t1 :===: t2) ::: _ :@ cause)
            | stuck t1                 -> tell (Set.singleton q)
            | stuck t2                 -> tell (Set.singleton q)
            | span :| _ <- spans cause -> throwError (ElabError span mempty (TypeMismatch (Set.singleton q)))
        freshName = ((,) <*> pure) . qlocal <$> gensym ""
        exists = pure . Meta <$> gensym "_meta_"

        stuck (Meta _ :$ _) = True
        stuck _             = False


solver :: ( Carrier sig m
          , Effect sig
          , Member (Error SolverError) sig
          , Member Naming sig
          , Member (Reader Scope) sig
          )
       => Set.Set HomConstraint
       -> m Substitution
solver constraints = execState Map.empty $ do
  queue <- execState (Seq.empty :: Queue) $ do
    stuck <- fmap fold . execState (Map.empty :: Blocked) $ do
      enqueueAll constraints
      step
    unless (null stuck) (throwError (StuckConstraints (toList stuck)))
  unless (null queue) (throwError (StalledConstraints (toList queue)))

step :: ( Carrier sig m
        , Effect sig
        , Member (Error SolverError) sig
        , Member Naming sig
        , Member (Reader Scope) sig
        , Member (State Blocked) sig
        , Member (State Queue) sig
        , Member (State Substitution) sig
        )
     => m ()
step = do
  _S <- get
  dequeue >>= maybe (pure ()) (process _S >=> const step)

process :: ( Carrier sig m
           , Effect sig
           , Member (Error SolverError) sig
           , Member Naming sig
           , Member (Reader Scope) sig
           , Member (State Blocked) sig
           , Member (State Queue) sig
           , Member (State Substitution) sig
           )
        => Substitution
        -> HomConstraint
        -> m ()
process _S c@((_ :|-: (tm1 :===: tm2) ::: _) :~ _)
  | tm1 == tm2 = pure ()
  | s <- Map.restrictKeys _S (metaNames (fvs c)), not (null s) = simplify' (applyConstraint s c) >>= enqueueAll
  | Just (m, sp) <- pattern tm1 = solve (m := Value.lams sp tm2)
  | Just (m, sp) <- pattern tm2 = solve (m := Value.lams sp tm1)
  | otherwise = block c

block :: (Carrier sig m, Member (Error SolverError) sig, Member (State Blocked) sig) => HomConstraint -> m ()
block c = do
  let s = Set.singleton c
      mvars = metaNames (fvs c)
  when (null mvars) $ throwError (UnblockableConstraint c)
  modify (Map.unionWith (<>) (foldl' (\ m i -> Map.insertWith (<>) i s m) mempty mvars))

enqueueAll :: (Carrier sig m, Member (State Queue) sig, Foldable t) => t HomConstraint -> m ()
enqueueAll = modify . flip (foldl' (Seq.|>))

dequeue :: (Carrier sig m, Member (State Queue) sig) => m (Maybe HomConstraint)
dequeue = gets Seq.viewl >>= \case
  Seq.EmptyL -> pure Nothing
  h Seq.:< q -> Just h <$ put q

pattern :: Type Meta -> Maybe (Gensym, Stack Meta)
pattern (Meta m :$ sp) = (,) m <$> (traverse free sp >>= distinct)
pattern _              = Nothing

free :: Type a -> Maybe a
free (v :$ Nil) = Just v
free _          = Nothing

distinct :: (Foldable t, Ord a) => t a -> Maybe (t a)
distinct sp = sp <$ guard (length (foldMap Set.singleton sp) == length sp)

solve :: (Carrier sig m, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig) => Solution -> m ()
solve (m := v) = do
  modify (Map.insert m v . fmap (applyType (Map.singleton m v)))
  cs <- gets (fromMaybe Set.empty . Map.lookup m)
  enqueueAll cs
  modify (Map.delete m :: Blocked -> Blocked)

applyConstraint :: Substitution -> HomConstraint -> HomConstraint
applyConstraint subst ((ctx :|-: (tm1 :===: tm2) ::: ty) :~ span) = (applyContext subst ctx :|-: (applyType subst tm1 :===: applyType subst tm2) ::: applyType subst ty) :~ span

applyContext :: Substitution -> Context (Type Meta) -> Context (Type Meta)
applyContext = fmap . applyType

applyType :: Substitution -> Type Meta -> Type Meta
applyType subst ty = ty >>= \case
  Qual n -> pure (Qual n)
  Meta m -> fromMaybe (pure (Meta m)) (Map.lookup m subst)

simplify' :: ( Carrier sig m
            , Effect sig
            , Member (Error SolverError) sig
            , Member Naming sig
            , Member (Reader Scope) sig
            )
         => HomConstraint
         -> m (Set.Set HomConstraint)
simplify' (constraint :~ span) = execWriter (go constraint)
  where go = \case
          _ :|-: (tm1 :===: tm2) ::: _ | tm1 == tm2 -> pure ()
          ctx :|-: (Pi p1 _ t1 b1 :===: Pi p2 _ t2 b2) ::: Type
            | p1 == p2 -> do
              go (ctx :|-: (t1 :===: t2) ::: Type)
              n <- gensym "simplify"
              -- FIXME: this should insert some sort of dependency
              go (Context.insert (n ::: t1) ctx :|-: (Value.instantiate (pure (qlocal n)) b1 :===: Value.instantiate (pure (qlocal n)) b2) ::: Type)
          ctx :|-: (Pi Im _ t1 b1 :===: tm2) ::: Type -> do
            n <- exists t1
            go (ctx :|-: (Value.instantiate n b1 :===: tm2) ::: Type)
          ctx :|-: (tm1 :===: Pi Im _ t2 b2) ::: Type -> do
            n <- exists t2
            go (ctx :|-: (tm1 :===: Value.instantiate n b2) ::: Type)
          ctx :|-: (Lam f1 :===: Lam f2) ::: Pi _ _ t b -> do
            n <- gensym "simplify"
            go (Context.insert (n ::: t) ctx :|-: (Value.instantiate (pure (qlocal n)) f1 :===: Value.instantiate (pure (qlocal n)) f2) ::: Value.instantiate (pure (qlocal n)) b)
          ctx :|-: (f1@(Qual (_ :.: _)) :$ sp1 :===: f2@(Qual (_ :.: _)) :$ sp2) ::: ty -> do
            t1 <- whnf (f1 :$ sp1)
            t2 <- whnf (f2 :$ sp2)
            go (ctx :|-: (t1 :===: t2) ::: ty)
          ctx :|-: (f1@(Qual (_ :.: _)) :$ sp1 :===: t2) ::: ty -> do
            t1 <- whnf (f1 :$ sp1)
            go (ctx :|-: (t1 :===: t2) ::: ty)
          ctx :|-: (t1 :===: f2@(Qual (_ :.: _)) :$ sp2) ::: ty -> do
            t2 <- whnf (f2 :$ sp2)
            go (ctx :|-: (t1 :===: t2) ::: ty)
          ctx :|-: (tm1 :===: Lam b2) ::: ty | False -> do
            n <- gensym "simplify"
            go (ctx :|-: (lam (qlocal n) (tm1 $$ pure (qlocal n)) :===: Lam b2) ::: ty)
          ctx :|-: (Lam b1 :===: tm2) ::: ty | False -> do
            n <- gensym "simplify"
            go (ctx :|-: (Lam b1 :===: lam (qlocal n) (tm2 $$ pure (qlocal n))) ::: ty)
          c@(_ :|-: (t1 :===: t2) ::: _)
            | stuck t1 || stuck t2 -> tell (Set.singleton (c :~ span))
            | otherwise            -> throwError (UnsimplifiableConstraint (c :~ span))

        exists _ = pure . Meta <$> gensym "_meta_"

        stuck (Meta _ :$ _) = True
        stuck _             = False

hetToHom :: HetConstraint -> Set.Set HomConstraint
hetToHom ((ctx :|-: tm1 ::: ty1 :===: tm2 ::: ty2) :~ span) = Set.fromList
  -- FIXME: represent dependency of second on first
  [ (ctx :|-: (ty1 :===: ty2) ::: Type) :~ span
  , (ctx :|-: (tm1 :===: tm2) ::: ty1)  :~ span
  ]


data SolverError
  = UnsimplifiableConstraint HomConstraint
  | UnblockableConstraint HomConstraint
  | UnsolvedMetavariable Gensym
  | StuckConstraints [HomConstraint]
  | StalledConstraints [HomConstraint]
  deriving (Eq, Ord, Show)

instance Pretty SolverError where
  pretty = \case
    UnsimplifiableConstraint ((ctx :|-: eqn) :~ span) -> prettyErr span (pretty "unsimplifiable constraint" </> pretty eqn) (prettyEqn eqn : prettyCtx ctx)
    UnblockableConstraint ((ctx :|-: eqn) :~ span) -> prettyErr span (pretty "cannot block constraint without metavars" <+> prettyEqn eqn) (prettyCtx ctx)
    UnsolvedMetavariable meta -> prettyErr (Span mempty mempty mempty) (pretty "unsolved metavariable" <+> pretty meta) []
    StuckConstraints constraints -> fold (intersperse hardline (map stuck constraints))
      where stuck ((ctx :|-: eqn) :~ span) = prettyErr span (pretty "stuck constraint" </> pretty eqn) (prettyCtx ctx)
    StalledConstraints constraints -> fold (intersperse hardline (map stalled constraints))
      where stalled ((ctx :|-: eqn) :~ span) = prettyErr span (pretty "stalled constraint" </> pretty eqn) (prettyCtx ctx)
    where prettyCtx ctx = if null ctx then [] else [nest 2 (vsep [pretty "Local bindings:", pretty ctx])]
          prettyEqn ((expected :===: actual) ::: ty) = fold (punctuate hardline
            [ pretty "expected:" <+> pretty expected
            , pretty "  actual:" <+> pretty actual
            , pretty " at type:" <+> pretty ty
            ])

instance PrettyPrec SolverError
