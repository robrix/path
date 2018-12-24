{-# LANGUAGE DeriveTraversable, FlexibleContexts #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Reader
import Control.Effect.State
import qualified Path.Context as Context
import Path.Core
import Path.Name
import Path.Subst
import qualified Path.Term as Term

data Back a = Nil | Back a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


type Term = Term.Term (Core QName) ()
type Type = Context.Type QName

data Twin = Only | TwinL | TwinR
  deriving (Eq, Ord, Show)

data Equation = (Term, Type) :==: (Term, Type)
  deriving (Eq, Ord, Show)

sym :: Equation -> Equation
sym (s :==: t) = t :==: s

data Param = P Type | Type :++: Type
  deriving (Eq, Ord, Show)

type Params = Back (Name, Param)

data Dec a = Hole | Defn a
  deriving (Eq, Ord, Show)

data Entry tm
  = E QName Type (Dec tm)
  | Q Status Problem
  deriving (Eq, Ord, Show)

data Status = Blocked | Active
  deriving (Eq, Ord, Show)

data Problem
  = Unify Equation
  | All Param QName Problem
  deriving (Eq, Ord, Show)


popL :: (Carrier sig m, Member (State (Back (Entry tm))) sig, Monad m) => m (Entry tm)
popL = do
  entries <- get
  case entries of
    es :> e -> e <$ put es
    Nil     -> error "popL: empty context"

pushL :: (Carrier sig m, Member (State (Back (Entry tm))) sig, Monad m) => Entry tm -> m ()
pushL e = modify (:> e)


popR :: (Carrier sig m, Member (State [Either (Subst QName tm) (Entry tm)]) sig, Monad m) => m (Maybe (Either (Subst QName tm) (Entry tm)))
popR = do
  entries <- get
  case entries of
    e : es -> Just e <$ put es
    []     -> pure Nothing

pushR :: (Carrier sig m, Member (State [Either (Subst QName tm) (Entry tm)]) sig, Monad m) => Either (Subst QName tm) (Entry tm) -> m ()
pushR e = modify (e:)


askParams :: (Carrier sig m, Member (Reader Params) sig) => m Params
askParams = ask

localParams :: (Carrier sig m, Member (Reader Params) sig) => (Params -> Params) -> m a -> m a
localParams = local
