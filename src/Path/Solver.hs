{-# LANGUAGE FlexibleContexts, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Solver where

import           Control.Effect
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Writer
import           Control.Monad ((>=>), guard, unless)
import           Data.Foldable (foldl', toList)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Path.Constraint hiding (Scope(..))
import           Path.Context as Context
import           Path.Error
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Scope as Scope hiding (null)
import           Path.Stack
import           Path.Value as Value hiding (Scope (..))
import           Prelude hiding (pi)
import           Text.Trifecta.Rendering (Spanned(..))

type Blocked = Set.Set (Spanned (Constraint Meta))
type Queue = Seq.Seq (Spanned (Constraint Meta))

-- FIXME: we need constraint dependencies to ensure that we e.g. δ-reduce a type like Either L R and solve the π type unification constraint before we try to solve whatever we typed using it

simplify :: ( Carrier sig m
            , Effect sig
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (Reader Scope) sig
            )
         => Spanned (Constraint Meta)
         -> m (Set.Set (Spanned (Constraint Meta)))
simplify (constraint :~ span) = do
  scope <- ask
  (ctx, eqn) <- unbinds constraint
  execWriter (go scope ctx eqn)
  where go scope ctx = \case
          (tm1 :===: tm2) ::: _ | tm1 == tm2 -> pure ()
          (Meta m1 :$ _ :===: Meta m2 :$ _) ::: _
            | m1 == m2 -> pure ()
          c@((t1 :===: t2) ::: _)
            | blocked t1 || blocked t2 -> tell (Set.singleton (binds ctx c :~ span))
          (Pi (p1 :< (_, t1)) b1 :===: Pi (p2 :< (_, t2)) b2) ::: Type
            | p1 == p2 -> do
              go scope ctx ((t1 :===: t2) ::: Type)
              n <- gensym "pi"
              -- FIXME: this should insert some sort of dependency
              go scope (Context.insert (n ::: t1) ctx) ((Value.instantiate (pure (qlocal n)) b1 :===: Value.instantiate (pure (qlocal n)) b2) ::: Type)
          (Pi (Im :< (_, t1)) b1 :===: tm2) ::: Type -> do
            n <- exists ctx t1
            go scope ctx ((Value.instantiate n b1 :===: tm2) ::: Type)
          (tm1 :===: Pi (Im :< (_, t2)) b2) ::: Type -> do
            n <- exists ctx t2
            go scope ctx ((tm1 :===: Value.instantiate n b2) ::: Type)
          (Lam p1 f1 :===: Lam p2 f2) ::: Pi (pt :< (_, t)) b
            | p1 == p2, p1 == pt -> do
              n <- gensym "lam"
              go scope (Context.insert (n ::: t) ctx) ((Value.instantiate (pure (qlocal n)) f1 :===: Value.instantiate (pure (qlocal n)) f2) ::: Value.instantiate (pure (qlocal n)) b)
          (t1 :===: t2) ::: Pi (Im :< (u, t)) b -> do
            n <- qlocal <$> gensym "lam"
            go scope ctx ((Value.lam (Im :< n) t1 :===: Value.lam (Im :< n) t2) ::: Pi (Im :< (u, t)) b)
          (f1@(Name (Global _)) :$ sp1 :===: f2@(Name (Global _)) :$ sp2) ::: ty
            | Just t1 <- whnf scope (f1 :$ sp1)
            , Just t2 <- whnf scope (f2 :$ sp2) ->
              go scope ctx ((t1 :===: t2) ::: ty)
          (f1@(Name (Global _)) :$ sp1 :===: t2) ::: ty
            | Just t1 <- whnf scope (f1 :$ sp1) ->
              go scope ctx ((t1 :===: t2) ::: ty)
          (t1 :===: f2@(Name (Global _)) :$ sp2) ::: ty
            | Just t2 <- whnf scope (f2 :$ sp2) ->
              go scope ctx ((t1 :===: t2) ::: ty)
          (Name (Local f1) :$ sp1 :===: Name (Local f2) :$ sp2) ::: _
            | f1 == f2
            , length sp1 == length sp2 -> do
              let simplifySpine ctx ty ((_ :< a1, _ :< a2) : as) = do
                    n <- gensym "spine"
                    case Value.unpi (qlocal n) ty of
                      Just (_ ::: t, b) -> go scope ctx ((a1 :===: a2) ::: t) >> simplifySpine (Context.insert (n ::: t) ctx) b as
                      Nothing -> pure ()
                  simplifySpine _ _ _ = pure ()
              t <- maybe (runReader span (freeVariable (qlocal f1))) pure (Context.lookup f1 ctx)
              simplifySpine ctx t (zip (toList sp1) (toList sp2))
          (tm1 :===: Lam p2 b2) ::: ty@(Pi (_ :< (_, _)) _) -> do
            n <- gensym "lam"
            go scope ctx ((lam (p2 :< qlocal n) (tm1 $$ (p2 :< pure (qlocal n))) :===: Lam p2 b2) ::: ty)
          (Lam p1 b1 :===: tm2) ::: ty@(Pi (_ :< (_, _)) _) -> do
            n <- gensym "lam"
            go scope ctx ((Lam p1 b1 :===: lam (p1 :< qlocal n) (tm2 $$ (p1 :< pure (qlocal n)))) ::: ty)
          c@((t1 :===: t2) ::: _)
            | blocked t1 || blocked t2 -> tell (Set.singleton (binds ctx c :~ span))
            | otherwise                -> unsimplifiableConstraint [binds ctx c :~ span]

        exists ctx _ = do
          n <- Meta <$> gensym "meta"
          pure (pure n Value.$$* ((Ex :<) . pure . qlocal <$> Context.vars ctx))

        blocked (Meta _ :$ _) = True
        blocked _             = False

        whnf scope (Name (Global n) Value.:$ sp) = do
          entry <- Scope.lookup n scope
          val <- entryValue entry
          let val' = weaken val $$* sp
          maybe (pure val') pure (whnf scope val')
        whnf _ _ = Nothing

solver :: ( Carrier sig m
          , Effect sig
          , Member (Error Doc) sig
          , Member Naming sig
          , Member (Reader Scope) sig
          )
       => Set.Set (Spanned (Constraint Meta))
       -> m Substitution
solver constraints = execState Map.empty $ do
  queue <- execState (Seq.empty :: Queue) . evalState (Set.empty :: Blocked) $ do
    enqueueAll constraints
    step
  unless (null queue) (stalledConstraints (toList queue))

step :: ( Carrier sig m
        , Effect sig
        , Member (Error Doc) sig
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
           , Member (Error Doc) sig
           , Member Naming sig
           , Member (Reader Scope) sig
           , Member (State Blocked) sig
           , Member (State Queue) sig
           , Member (State Substitution) sig
           )
        => Substitution
        -> Spanned (Constraint Meta)
        -> m ()
process _S c@(constraint :~ _) = do
  (_, (tm1 :===: tm2) ::: _) <- unbinds constraint
  case () of
    _ | tm1 == tm2 -> pure ()
      | s <- Map.restrictKeys _S (metaNames (fvs c)), not (null s) -> simplify (apply s c) >>= enqueueAll
      | Just (m, sp) <- pattern tm1 -> solve m (Value.lams sp tm2)
      | Just (m, sp) <- pattern tm2 -> solve m (Value.lams sp tm1)
      | otherwise -> block c

block :: (Carrier sig m, Member (State Blocked) sig) => Spanned (Constraint Meta) -> m ()
block c = modify (Set.insert c)

enqueueAll :: (Carrier sig m, Member (State Queue) sig, Foldable t) => t (Spanned (Constraint Meta)) -> m ()
enqueueAll = modify . flip (foldl' (Seq.|>))

dequeue :: (Carrier sig m, Member (State Queue) sig) => m (Maybe (Spanned (Constraint Meta)))
dequeue = gets Seq.viewl >>= \case
  Seq.EmptyL -> pure Nothing
  h Seq.:< q -> Just h <$ put q

pattern :: Type Meta -> Maybe (Gensym, Stack (Plicit Meta))
pattern (Meta m :$ sp) = (,) m <$> (traverse (traverse free) sp >>= distinct)
pattern _              = Nothing

free :: Type a -> Maybe a
free (v :$ Nil) = Just v
free _          = Nothing

distinct :: (Foldable t, Ord a) => t a -> Maybe (t a)
distinct sp = sp <$ guard (length (foldMap Set.singleton sp) == length sp)

solve :: (Carrier sig m, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig) => Gensym -> Value Meta -> m ()
solve m v = do
  modify (Map.insert m v . fmap (apply (Map.singleton m v)))
  (unblocked, blocked) <- gets (Set.partition (isBlockedOn (Meta m)))
  enqueueAll unblocked
  put blocked

isBlockedOn :: Meta -> Spanned (Constraint Meta) -> Bool
isBlockedOn m = Set.member m . fvs
