{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Solver where

import           Control.Effect
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Writer
import           Control.Monad ((>=>), guard, unless)
import           Data.Bifunctor (first)
import           Data.Foldable (foldl', toList)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Data.Void
import           Path.Constraint
import           Path.Context as Context
import           Path.Core as Core
import           Path.Error
import           Path.Module as Module
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Scope
import           Path.Span (Spanned(..), unSpanned)
import           Path.Stack
import           Path.Usage
import           Prelude hiding (pi)

type Blocked = Set.Set (Spanned (Constraint Core (Name Meta)))
type Queue = Seq.Seq (Spanned (Constraint Core (Name Meta)))

-- FIXME: we need constraint dependencies to ensure that we e.g. δ-reduce a type like Either L R and solve the π type unification constraint before we try to solve whatever we typed using it

simplify :: ( Carrier sig m
            , Effect sig
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (Reader (ModuleGraph Core Void)) sig
            , Member (State Signature) sig
            , Member (Writer [Spanned (Constraint Core (Name Meta))]) sig
            )
         => Spanned (Constraint Core (Name Meta))
         -> m (Set.Set (Spanned (Constraint Core (Name Meta))))
simplify (constraint :~ span) = do
  scope <- ask @(ModuleGraph Core Void)
  (ctx, eqn) <- unbinds constraint
  execWriter (go scope ctx eqn)
  where go scope ctx = \case
          (tm1 :===: tm2) ::: _ | tm1 == tm2 -> pure ()
          (Local (Meta m1) :$ _ :===: Local (Meta m2) :$ _) ::: _
            | m1 == m2 -> pure ()
          c@((t1 :===: t2) ::: _)
            | blocked t1 || blocked t2 -> tell (Set.singleton (binds (first (Local . Name) <$> unContext ctx) c :~ span))
          (Pi (p1 :< _ :@ t1) b1 :===: Pi (p2 :< _ :@ t2) b2) ::: Type
            | p1 == p2 -> do
              go scope ctx ((t1 :===: t2) ::: Type)
              n <- fresh
              -- FIXME: this should insert some sort of dependency
              go scope (Context.insert (n ::: t1) ctx) ((instantiate1 (pure (Local (Name n))) b1 :===: instantiate1 (pure (Local (Name n))) b2) ::: Type)
          (Pi (Im :< _ :@ t1) b1 :===: tm2) ::: Type -> do
            n <- exists ctx t1
            go scope ctx ((instantiate1 n b1 :===: tm2) ::: Type)
          (tm1 :===: Pi (Im :< _ :@ t2) b2) ::: Type -> do
            n <- exists ctx t2
            go scope ctx ((tm1 :===: instantiate1 n b2) ::: Type)
          (Lam p1 f1 :===: Lam p2 f2) ::: Pi (pt :< _ :@ t) b
            | p1 == p2, p1 == pt -> do
              n <- fresh
              go scope (Context.insert (n ::: t) ctx) ((instantiate1 (pure (Local (Name n))) f1 :===: instantiate1 (pure (Local (Name n))) f2) ::: instantiate1 (pure (Local (Name n))) b)
          (t1 :===: t2) ::: Pi (Im :< u :@ t) b -> do
            n <- Local . Name <$> fresh
            go scope ctx ((Core.lam (Im :< n) t1 :===: Core.lam (Im :< n) t2) ::: Pi (Im :< u :@ t) b)
          (f1@(Global _) :$ sp1 :===: f2@(Global _) :$ sp2) ::: ty
            | Just t1 <- whnf scope (f1 :$ sp1)
            , Just t2 <- whnf scope (f2 :$ sp2) ->
              go scope ctx ((t1 :===: t2) ::: ty)
          (f1@(Global _) :$ sp1 :===: t2) ::: ty
            | Just t1 <- whnf scope (f1 :$ sp1) ->
              go scope ctx ((t1 :===: t2) ::: ty)
          (t1 :===: f2@(Global _) :$ sp2) ::: ty
            | Just t2 <- whnf scope (f2 :$ sp2) ->
              go scope ctx ((t1 :===: t2) ::: ty)
          (Local (Name f1) :$ sp1 :===: Local (Name f2) :$ sp2) ::: _
            | f1 == f2
            , length sp1 == length sp2 -> do
              let simplifySpine ctx ty ((_ :< a1, _ :< a2) : as) = do
                    n <- fresh
                    case Core.unpi (Local (Name n)) ty of
                      Just (_ :< _ ::: _ :@ t, b) -> go scope ctx ((a1 :===: a2) ::: t) >> simplifySpine (Context.insert (n ::: t) ctx) b as
                      Nothing                     -> pure ()
                  simplifySpine _ _ _ = pure ()
              t <- maybe (runReader span (freeVariable (Name f1))) pure (Context.lookup f1 ctx)
              simplifySpine ctx t (zip (toList sp1) (toList sp2))
          (tm1 :===: Lam p2 b2) ::: ty@Pi{} -> do
            n <- fresh
            go scope ctx ((lam (p2 :< Local (Name n)) (tm1 $$ (p2 :< pure (Local (Name n)))) :===: Lam p2 b2) ::: ty)
          (Lam p1 b1 :===: tm2) ::: ty@Pi{} -> do
            n <- fresh
            go scope ctx ((Lam p1 b1 :===: lam (p1 :< Local (Name n)) (tm2 $$ (p1 :< pure (Local (Name n))))) ::: ty)
          c@((t1 :===: t2) ::: _)
            | blocked t1 || blocked t2 -> tell (Set.singleton (binds (first (Local . Name) <$> unContext ctx) c :~ span))
            | otherwise                -> tell [binds (first (Local . Name) <$> unContext ctx) c :~ span]

        exists ctx ty = do
          n <- fresh
          let f (n ::: t) = Ex :< Local (Name n) ::: More :@ t
              ty' = Core.pis (f <$> Context.unContext ctx) ty
          modify (Signature . Map.insert n ty' . unSignature)
          pure (pure (Local (Meta n)) Core.$$* ((Ex :<) . pure . Local . Name <$> Context.vars ctx))

        blocked (Local (Meta _) :$ _) = True
        blocked _                     = False

        whnf scope (Global n Core.:$ sp) = do
          val <- unSpanned . declTerm <$> Module.lookup n scope
          let val' = weaken val $$* sp
          maybe (pure val') pure (whnf scope val')
        whnf _ _ = Nothing

solver :: ( Carrier sig m
          , Effect sig
          , Member (Error Doc) sig
          , Member Naming sig
          , Member (Reader (ModuleGraph Core Void)) sig
          , Member (State Signature) sig
          )
       => Set.Set (Spanned (Constraint Core (Name Meta)))
       -> m Substitution
solver constraints = execState mempty $ do
  (queue, unsimplifiable) <- runState (Seq.empty :: Queue) . evalState (Set.empty :: Blocked) . execWriter $ do
    enqueueAll constraints
    step
  sig <- get
  unless (null unsimplifiable && null queue) (unsimplifiableConstraints sig (unsimplifiable <> toList queue))

step :: ( Carrier sig m
        , Effect sig
        , Member (Error Doc) sig
        , Member Naming sig
        , Member (Reader (ModuleGraph Core Void)) sig
        , Member (State Blocked) sig
        , Member (State Queue) sig
        , Member (State Signature) sig
        , Member (State Substitution) sig
        , Member (Writer [Spanned (Constraint Core (Name Meta))]) sig
        )
     => m ()
step = do
  _S <- get
  dequeue >>= maybe (pure ()) (process _S >=> const step)

process :: ( Carrier sig m
           , Effect sig
           , Member (Error Doc) sig
           , Member Naming sig
           , Member (Reader (ModuleGraph Core Void)) sig
           , Member (State Blocked) sig
           , Member (State Queue) sig
           , Member (State Signature) sig
           , Member (State Substitution) sig
           , Member (Writer [Spanned (Constraint Core (Name Meta))]) sig
           )
        => Substitution
        -> Spanned (Constraint Core (Name Meta))
        -> m ()
process (Substitution _S) c@(constraint :~ _) = do
  (_, (tm1 :===: tm2) ::: _) <- unbinds constraint
  let s = Map.restrictKeys _S (metaNames (localNames (fvs constraint)))
      go | not (null s)                = simplify (apply (Substitution s) c) >>= enqueueAll
         | Just (m, sp) <- pattern tm1 = solve m (Core.lams (fmap Local <$> sp) tm2)
         | Just (m, sp) <- pattern tm2 = solve m (Core.lams (fmap Local <$> sp) tm1)
         | otherwise                   = block c
  unless (tm1 == tm2) go

block :: (Carrier sig m, Member (State Blocked) sig) => Spanned (Constraint Core (Name Meta)) -> m ()
block c = modify (Set.insert c)

enqueueAll :: (Carrier sig m, Member (State Queue) sig, Foldable t) => t (Spanned (Constraint Core (Name Meta))) -> m ()
enqueueAll = modify . flip (foldl' (Seq.|>))

dequeue :: (Carrier sig m, Member (State Queue) sig) => m (Maybe (Spanned (Constraint Core (Name Meta))))
dequeue = gets Seq.viewl >>= \case
  Seq.EmptyL -> pure Nothing
  h Seq.:< q -> Just h <$ put q

pattern :: Core (Name Meta) -> Maybe (Gensym, Stack (Plicit Meta))
pattern (Local (Meta m) :$ sp) = (,) m <$> (traverse (traverse bound) sp >>= distinct)
pattern _                      = Nothing

bound :: Core (Name Meta) -> Maybe Meta
bound (Local v :$ Nil) = Just v
bound _                = Nothing

distinct :: (Foldable t, Ord a) => t a -> Maybe (t a)
distinct sp = sp <$ guard (length (foldMap Set.singleton sp) == length sp)

solve :: ( Carrier sig m
         , Member (State Blocked) sig
         , Member (State Queue) sig
         , Member (State Signature) sig
         , Member (State Substitution) sig
         )
      => Gensym
      -> Core (Name Meta)
      -> m ()
solve m v = do
  let subst = Substitution (Map.singleton m v)
  modify (Substitution . Map.insert m v . fmap (apply subst) . unSubstitution)
  modify (Signature . fmap (apply subst) . unSignature)
  (unblocked, blocked) <- gets (Set.partition (isBlockedOn (Meta m)))
  enqueueAll unblocked
  put blocked

isBlockedOn :: Meta -> Spanned (Constraint Core (Name Meta)) -> Bool
isBlockedOn m = Set.member (Local m) . foldMap fvs
