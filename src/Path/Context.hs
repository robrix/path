module Path.Context where

import Control.Arrow ((&&&))
import Data.Foldable (toList)
import qualified Data.Set as Set
import Path.Stack as Stack
import Path.Name
import Path.Pretty
import Path.Value

newtype Context = Context { unContext :: Stack (Typed Gensym) }
  deriving (Eq, Ord, Show)

null :: Context -> Bool
null = Prelude.null . unContext

lookup :: Gensym -> Context -> Maybe Type
lookup n = fmap typedType . Stack.find ((== n) . typedTerm) . unContext

insert :: Typed Gensym -> Context -> Context
insert t = Context . (:> t) . unContext

union :: Context -> Context -> Context
union (Context c1) (Context c2) = Context (c1 <> c2)

filter :: (Typed Gensym -> Bool) -> Context -> Context
filter f = Context . Stack.filter f . unContext

boundVars :: Context -> Set.Set Gensym
boundVars = foldMap (Set.singleton . typedTerm) . unContext

nub :: Context -> Context
nub = Context . go mempty . unContext
  where go _ Nil = Nil
        go v (init :> last)
          | typedTerm last `Set.member` v = go v init
          | otherwise                     = go (Set.insert (typedTerm last) v) init :> last

instance Pretty Context where
  pretty = tabulate2 (space <> colon <> space) . map (green . pretty . typedTerm &&& nest 2 . align . group . pretty . typedType) . toList . unContext

instance PrettyPrec Context

instance Semigroup Context where
  Context c1 <> Context c2 = Context (c1 <> c2)

instance Monoid Context where
  mempty = Context Nil
