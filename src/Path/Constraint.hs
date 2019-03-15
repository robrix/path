{-# LANGUAGE FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Constraint where

import Data.List.NonEmpty (NonEmpty(..), toList)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Path.Context
import Path.Name
import Path.Pretty
import Path.Value
import Text.Trifecta.Rendering (Span, Spanned(..))

data Equation a
  = a :===: a
  deriving (Eq, Ord, Show)

infix 3 :===:

instance Pretty a => Pretty (Equation a) where
  pretty (t1 :===: t2) = flatAlt (align (space <+> pretty t1 </> eq <+> pretty t2)) (pretty t1 <+> eq <+> pretty t2)
    where eq = magenta (pretty "≡")

instance Pretty a => PrettyPrec (Equation a)

instance FreeVariables v a => FreeVariables v (Equation a) where
  fvs (a1 :===: a2) = fvs a1 <> fvs a2


type HetConstraint = Spanned (Contextual (Equation (Value Meta ::: Type Meta)))
type HomConstraint = Spanned (Contextual (Equation (Value Meta) ::: Type Meta))


data Cause
  = Assert Span
  | Via (Equation (Value Meta) ::: Type Meta) Cause
  | Cause :<>: Cause
  deriving (Eq, Ord, Show)

instance Semigroup Cause where
  (<>) = (:<>:)

spans :: Cause -> NonEmpty Span
spans = flip go []
  where go (Assert span) = (span :|)
        go (Via _ cause) = go cause
        go (l :<>: r)    = go l . toList . go r


data Caused a
  = a :@ Cause
  deriving (Eq, Ord, Show)

infix 0 :@

instance FreeVariables v a => FreeVariables v (Caused a) where
  fvs (a :@ _) = fvs a

cause :: Caused a -> Cause
cause (_ :@ cause) = cause


type Substitution = Map.Map Gensym (Value Meta)

class Substitutable t where
  apply :: Substitution -> t -> t

unMeta :: Meta -> Maybe Gensym
unMeta (Meta n) = Just n
unMeta _        = Nothing

instance Substitutable (Value Meta) where
  apply subst val = do
    var <- val
    fromMaybe (pure var) (unMeta var >>= (subst Map.!?))

instance Substitutable a => Substitutable (Equation a) where
  apply subst (s1 :===: s2) = apply subst s1 :===: apply subst s2

instance (Substitutable a, Substitutable b) => Substitutable (a ::: b) where
  apply subst (tm ::: ty) = apply subst tm ::: apply subst ty

instance (Ord a, Substitutable a) => Substitutable (Set.Set a) where
  apply subst = Set.map (apply subst)

instance Substitutable a => Substitutable (Spanned a) where
  apply subst (a :~ span) = apply subst a :~ span

instance Substitutable a => Substitutable (Context a) where
  apply subst = fmap (apply subst)

instance Substitutable a => Substitutable (Contextual a) where
  apply subst (ctx :|-: a) = apply subst ctx :|-: apply subst a
