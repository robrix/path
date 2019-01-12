{-# LANGUAGE LambdaCase, MultiParamTypeClasses #-}
module Path.Surface where

import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Usage
import Text.Trifecta.Rendering (Span)

data Surface
  = Var UName
  | Lam (Maybe UName) Surface
  | Surface :$ Surface
  | Type
  | Pi (Maybe UName) Plicity Usage Surface Surface
  | Hole UName
  | (Usage, Surface) :-> Surface
  | Ann Span Surface
  deriving (Eq, Ord, Show)

instance FreeVariables UName Surface where
  fvs = \case
    Var v -> Set.singleton v
    Lam (Just v) b -> Set.delete v (fvs b)
    Lam Nothing  b -> fvs b
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi (Just v) _ _ t b -> fvs t <> Set.delete v (fvs b)
    Pi Nothing  _ _ t b -> fvs t <> fvs b
    Hole v -> Set.singleton v
    (_, a) :-> b -> fvs a <> fvs b
    Ann _ a -> fvs a
