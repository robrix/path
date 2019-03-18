{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators #-}
module Path.Context where

import Control.Arrow ((&&&))
import Data.Foldable (toList)
import qualified Data.Set as Set
import Path.Stack as Stack
import Path.Name
import Path.Pretty
import Path.Value

newtype Context a = Context { unContext :: Stack (Local ::: a) }
  deriving (Eq, Foldable, Functor, Monoid, Ord, Semigroup, Show, Traversable)

lookup :: Local -> Context a -> Maybe a
lookup n = fmap typedType . Stack.find ((== n) . typedTerm) . unContext

insert :: Local ::: a -> Context a -> Context a
insert t = Context . (:> t) . unContext

union :: Context a -> Context a -> Context a
union (Context c1) (Context c2) = Context (c1 <> c2)

filter :: (Local ::: a -> Bool) -> Context a -> Context a
filter f = Context . Stack.filter f . unContext

boundVars :: Context a -> Set.Set Local
boundVars = foldMap (Set.singleton . typedTerm) . unContext

nub :: Context a -> Context a
nub = Context . go mempty . unContext
  where go _ Nil = Nil
        go v (init :> last)
          | typedTerm last `Set.member` v = go v init
          | otherwise                     = go (Set.insert (typedTerm last) v) init :> last

vars :: Context a -> Stack Local
vars = fmap typedTerm . unContext


instance Pretty a => Pretty (Context a) where
  pretty = tabulate2 (space <> colon <> space) . map (green . pretty . typedTerm &&& nest 2 . align . group . pretty . typedType) . toList . unContext

instance Pretty a => PrettyPrec (Context a)

instance FreeVariables v a => FreeVariables v (Context a) where
  fvs = foldMap fvs


data Contextual a = Context (Type Meta) :|-: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 1 :|-:

instance Pretty a => Pretty (Contextual a) where
  pretty (ctx :|-: a) = pretty a </> pretty ctx

instance Pretty a => PrettyPrec (Contextual a)

instance FreeVariables Meta a => FreeVariables Meta (Contextual a) where
  fvs (ctx :|-: b) = fvs ctx <> fvs b
