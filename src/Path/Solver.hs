{-# LANGUAGE FlexibleContexts, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Solver where

import           Control.Effect
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Writer
import           Control.Monad ((>=>), guard, unless)
import           Data.Foldable (foldl', toList)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Path.Constraint
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

type Blocked = Set.Set Constraint
type Queue = Seq.Seq Constraint

-- FIXME: we need constraint dependencies to ensure that we e.g. δ-reduce a type like Either L R and solve the π type unification constraint before we try to solve whatever we typed using it

simplify :: ( Carrier sig m
            , Effect sig
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (Reader Scope) sig
            , Member (State Blocked) sig
            , Member (State Queue) sig
            , Member (State Substitution) sig
            )
         => Constraint
         -> m (Set.Set Constraint)
simplify (constraint :~ span) = ask >>= \ scope -> execWriter (go scope constraint)
  where go scope = \case
          _ :|-: (tm1 :===: tm2) ::: _ | tm1 == tm2 -> pure ()
          _ :|-: (t1 :===: t2) ::: _
            | Just (m, sp) <- pattern t1 -> solve m (Value.lams sp t2)
            | Just (m, sp) <- pattern t2 -> solve m (Value.lams sp t1)
          ctx :|-: (Pi (p1 :< (_, t1)) b1 :===: Pi (p2 :< (_, t2)) b2) ::: Type
            | p1 == p2 -> do
              go scope (ctx :|-: (t1 :===: t2) ::: Type)
              n <- gensym "pi"
              -- FIXME: this should insert some sort of dependency
              go scope (Context.insert (n ::: t1) ctx :|-: (Value.instantiate (pure (qlocal n)) b1 :===: Value.instantiate (pure (qlocal n)) b2) ::: Type)
          ctx :|-: (Pi (Im :< (_, t1)) b1 :===: tm2) ::: Type -> do
            n <- exists t1
            go scope (ctx :|-: (Value.instantiate n b1 :===: tm2) ::: Type)
          ctx :|-: (tm1 :===: Pi (Im :< (_, t2)) b2) ::: Type -> do
            n <- exists t2
            go scope (ctx :|-: (tm1 :===: Value.instantiate n b2) ::: Type)
          ctx :|-: (Lam f1 :===: Lam f2) ::: Pi (_ :< (_, t)) b -> do
            n <- gensym "lam"
            go scope (Context.insert (n ::: t) ctx :|-: (Value.instantiate (pure (qlocal n)) f1 :===: Value.instantiate (pure (qlocal n)) f2) ::: Value.instantiate (pure (qlocal n)) b)
          ctx :|-: (f1@(Name (Global _)) :$ sp1 :===: f2@(Name (Global _)) :$ sp2) ::: ty
            | Just t1 <- whnf scope (f1 :$ sp1)
            , Just t2 <- whnf scope (f2 :$ sp2) -> do
              go scope (ctx :|-: (t1 :===: t2) ::: ty)
          ctx :|-: (f1@(Name (Global _)) :$ sp1 :===: t2) ::: ty
            | Just t1 <- whnf scope (f1 :$ sp1) -> do
              go scope (ctx :|-: (t1 :===: t2) ::: ty)
          ctx :|-: (t1 :===: f2@(Name (Global _)) :$ sp2) ::: ty
            | Just t2 <- whnf scope (f2 :$ sp2) -> do
              go scope (ctx :|-: (t1 :===: t2) ::: ty)
          ctx :|-: (tm1 :===: Lam b2) ::: ty@(Pi (_ :< (_, _)) _) -> do
            n <- gensym "lam"
            go scope (ctx :|-: (lam (qlocal n) (tm1 $$ pure (qlocal n)) :===: Lam b2) ::: ty)
          ctx :|-: (Lam b1 :===: tm2) ::: ty@(Pi (_ :< (_, _)) _) -> do
            n <- gensym "lam"
            go scope (ctx :|-: (Lam b1 :===: lam (qlocal n) (tm2 $$ pure (qlocal n))) ::: ty)
          c@(_ :|-: (t1 :===: t2) ::: _)
            | blocked t1 || blocked t2 -> tell (Set.singleton (c :~ span))
            | otherwise                -> unsimplifiableConstraint (c :~ span)

        exists _ = pure . Meta <$> gensym ""

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
       => Set.Set Constraint
       -> m Substitution
solver constraints = execState Map.empty $ do
  (queue, blocked) <- runState (Seq.empty :: Queue) . execState (Set.empty :: Blocked) $ do
    enqueueAll constraints
    step
  unless (null blocked) (blockedConstraints (toList blocked))
  unless (null queue)   (stalledConstraints (toList queue))

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
        -> Constraint
        -> m ()
process _S c@((_ :|-: (tm1 :===: tm2) ::: _) :~ _)
  | tm1 == tm2 = pure ()
  | s <- Map.restrictKeys _S (metaNames (fvs c)), not (null s) = simplify (apply s c) >>= enqueueAll
  | Just (m, sp) <- pattern tm1 = solve m (Value.lams sp tm2)
  | Just (m, sp) <- pattern tm2 = solve m (Value.lams sp tm1)
  | otherwise = block c

block :: (Carrier sig m, Member (State Blocked) sig) => Constraint -> m ()
block c = modify (Set.insert c)

enqueueAll :: (Carrier sig m, Member (State Queue) sig, Foldable t) => t Constraint -> m ()
enqueueAll = modify . flip (foldl' (Seq.|>))

dequeue :: (Carrier sig m, Member (State Queue) sig) => m (Maybe Constraint)
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

solve :: (Carrier sig m, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig) => Gensym -> Value Meta -> m ()
solve m v = do
  modify (Map.insert m v . fmap (apply (Map.singleton m v)))
  (unblocked, blocked) <- gets (Set.partition (isBlockedOn (Meta m)))
  enqueueAll unblocked
  put blocked

isBlockedOn :: Meta -> Constraint -> Bool
isBlockedOn m = Set.member m . fvs
