{-# LANGUAGE LambdaCase, MultiParamTypeClasses #-}
module Path.Surface where

import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Usage
import Text.Trifecta.Rendering (Span)

data Surface
  = Var User
  | Lam (Maybe User) Surface
  | Surface :$ Surface
  | Type
  | Pi (Plicit (Maybe User, Usage, Surface)) Surface
  | Hole User
  | (Usage, Surface) :-> Surface
  | Ann Span Surface
  deriving (Eq, Ord, Show)

instance FreeVariables User Surface where
  fvs = \case
    Var v -> Set.singleton v
    Lam (Just v) b -> Set.delete v (fvs b)
    Lam Nothing  b -> fvs b
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi (_ :< (Just v,  _, t)) b -> fvs t <> Set.delete v (fvs b)
    Pi (_ :< (Nothing, _, t)) b -> fvs t <> fvs b
    Hole v -> Set.singleton v
    (_, a) :-> b -> fvs a <> fvs b
    Ann _ a -> fvs a
