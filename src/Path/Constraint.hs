{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, KindSignatures, LambdaCase, MultiParamTypeClasses, TypeOperators, UndecidableInstances #-}
module Path.Constraint where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Sum
import Data.Coerce

newtype MetaVar = M Int
  deriving (Eq, Ord, Show)

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


runSolver :: Carrier sig m => Eff (SolverC m) a -> m a
runSolver = runSolverC . interpret

newtype SolverC m a = SolverC { runSolverC :: m a }

instance Carrier sig m => Carrier (Solver :+: sig) (SolverC m) where
  ret = SolverC . ret
  eff = SolverC . handleSum (eff . handleCoercible) (\case
    (:~~:) _ _ k -> runSolverC k)
