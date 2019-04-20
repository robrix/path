{-# LANGUAGE LambdaCase, MultiParamTypeClasses #-}
module Path.Surface where

import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Usage
import Text.Trifecta.Rendering (Spanned)

data Surface
  = Var User
  | Lam (Plicit (Maybe User)) (Spanned Surface)
  | Spanned Surface :$ Plicit (Spanned Surface)
  | Type
  | Pi (Plicit (Maybe User, Usage, Spanned Surface)) (Spanned Surface)
  | Hole User
  | (Usage, Spanned Surface) :-> Spanned Surface
  deriving (Eq, Ord, Show)

instance FreeVariables User Surface where
  fvs = \case
    Var v -> Set.singleton v
    Lam (_ :< Just v) b -> Set.delete v (fvs b)
    Lam (_ :< Nothing)  b -> fvs b
    f :$ (_ :< a) -> fvs f <> fvs a
    Type -> Set.empty
    Pi (_ :< (Just v,  _, t)) b -> fvs t <> Set.delete v (fvs b)
    Pi (_ :< (Nothing, _, t)) b -> fvs t <> fvs b
    Hole v -> Set.singleton v
    (_, a) :-> b -> fvs a <> fvs b
