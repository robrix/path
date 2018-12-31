{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Subst where

import Control.Effect
import Control.Effect.State
import qualified Data.IntMap as IntMap
import Path.Context
import Path.Core
import Path.Name
import Path.Resources
import Path.Term
import Path.Usage
import Path.Value

newtype Subst = Subst { getSubst :: IntMap.IntMap (Type QName) }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

insert :: Meta -> Type QName -> Subst -> Subst
insert (M m) t = Subst . IntMap.insert m t . getSubst

lookup :: Meta -> Subst -> Maybe (Type QName)
lookup (M m) = IntMap.lookup m . getSubst


runSubst :: (Carrier sig m, Effect sig, Functor m) => Eff (StateC Subst m) (Term (Core Name QName) (Type QName), Resources Usage) -> m (Term (Core Name QName) (Type QName), Resources Usage)
runSubst = fmap (\ (Subst s, (tm, res)) -> (substitute s tm, res)) . runState mempty
  where substitute s tm = case IntMap.minViewWithKey s of
          Just ((m, ty), rest) -> substitute rest (cata (run (Local (Meta (M m))) ty) tm)
          Nothing              -> tm
        run q ty core ann = In core (subst q ty ann)
