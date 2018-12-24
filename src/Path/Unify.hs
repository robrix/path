{-# LANGUAGE DeriveTraversable, FlexibleContexts #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Reader
import Control.Effect.State
import Path.Name
import Path.Subst

data Back a = Nil | Back a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Twin = Only | TwinL | TwinR
  deriving (Eq, Ord, Show)

data Equation tm ty = (tm, ty) :==: (tm, ty)
  deriving (Eq, Ord, Show)

sym :: Equation tm ty -> Equation tm ty
sym (s :==: t) = t :==: s

data Param ty = P ty | ty :++: ty
  deriving (Eq, Ord, Show)

type Params ty = Back (Name, Param ty)

data Dec a = Hole | Defn a
  deriving (Eq, Ord, Show)

data Entry tm ty
  = E QName ty (Dec tm)
  | Q Status (Problem tm ty)
  deriving (Eq, Ord, Show)

data Status = Blocked | Active
  deriving (Eq, Ord, Show)

data Problem tm ty
  = Unify (Equation tm ty)
  | All (Param ty) QName (Problem tm ty)
  deriving (Eq, Ord, Show)


popL :: (Carrier sig m, Member (State (Back (Entry tm ty))) sig, Monad m) => m (Entry tm ty)
popL = do
  entries <- get
  case entries of
    es :> e -> e <$ put es
    Nil     -> error "popL: empty context"

pushL :: (Carrier sig m, Member (State (Back (Entry tm ty))) sig, Monad m) => Entry tm ty -> m ()
pushL e = modify (:> e)


popR :: (Carrier sig m, Member (State [Either (Subst QName tm) (Entry tm ty)]) sig, Monad m) => m (Maybe (Either (Subst QName tm) (Entry tm ty)))
popR = do
  entries <- get
  case entries of
    e : es -> Just e <$ put es
    []     -> pure Nothing

pushR :: (Carrier sig m, Member (State [Either (Subst QName tm) (Entry tm ty)]) sig, Monad m) => Either (Subst QName tm) (Entry tm ty) -> m ()
pushR e = modify (e:)


askParams :: (Carrier sig m, Member (Reader (Params ty)) sig) => m (Params ty)
askParams = ask

localParams :: (Carrier sig m, Member (Reader (Params ty)) sig) => (Params ty -> Params ty) -> m a -> m a
localParams = local
