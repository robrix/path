{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, KindSignatures, LambdaCase, MultiParamTypeClasses, TypeOperators, UndecidableInstances #-}
module Path.Constraint where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Sum
import Data.Coerce
import Path.Name

data Constraint
  = Top
  | Constraint :/\: Constraint
  | MetaVar :==: MetaVar
  deriving (Eq, Ord, Show)

-- | 'Solver' effects specify constraint generation.
data Solver (m :: * -> *) a
  = (:~~:) MetaVar MetaVar a
  deriving (Functor)

instance HFunctor Solver where
  hmap _ = coerce

instance Effect Solver where
  handle state handler = coerce . fmap (handler . (<$ state))


(~~) :: (Carrier sig m, Member Solver sig) => MetaVar -> MetaVar -> m ()
m1 ~~ m2 = send (m1 :~~: m2 $ ret ())


runSolver :: (Carrier sig m, Effect sig, Functor m) => Eff (SolverC m) a -> m a
runSolver = fmap snd . flip runSolverC Top . interpret

newtype SolverC m a = SolverC { runSolverC :: Constraint -> m (Constraint, a) }

instance (Carrier sig m, Effect sig) => Carrier (Solver :+: sig) (SolverC m) where
  ret a = SolverC (\ c -> ret (c, a))
  eff op = SolverC (\ c -> handleSum (eff . handleState c runSolverC) (\case
    (:~~:) m1 m2 k -> runSolverC k (c :/\: (m1 :==: m2))) op)
