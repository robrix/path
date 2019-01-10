{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses #-}
module Path.Value where

import Control.Applicative (Alternative(..))
import Data.Foldable (foldl', toList)
import qualified Data.Set as Set
import Path.Stack as Stack
import qualified Path.Core as Core
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Term
import Path.Usage
import Prelude hiding (pi)

data Value
  = Type                         -- ^ @'Type' : 'Type'@.
  | Lam              Value Scope -- ^ A lambda abstraction.
  | Pi Plicity Usage Value Scope -- ^ A ∏ type, with a 'Usage' annotation.
  | Typed Head :$ Stack Value    -- ^ A neutral term represented as a function on the right and a list of arguments to apply it.
  deriving (Eq, Ord, Show)

newtype Scope = Scope Value
  deriving (Eq, Ord, Pretty, PrettyPrec, Show)

data Head
  = Free QName
  | Bound Int
  deriving (Eq, Ord, Show)

instance FreeVariables QName Head where
  fvs (Free q) = Set.singleton q
  fvs _        = mempty

instance Pretty Head where
  pretty (Free q) = pretty q
  pretty (Bound i) = prettyVar i

instance PrettyPrec Head

instance PrettyPrec Value where
  prettyPrec = go 0
    where go i d = \case
            Lam t b -> prettyParens (d > 0) $ align (group (cyan backslash <+> foldr (var (fvs b')) (line <> cyan dot <+> go i 0 b') as))
              where (as, b') = unlams (Lam t b)
                    var vs (n ::: _) rest
                      | Local n `Set.member` vs = pretty n   <+> rest
                      | otherwise               = pretty '_' <+> rest
            Type -> yellow (pretty "Type")
            Pi ie pi t b'
              | let v = Gensym "" i
                    b = instantiate (free (Local v ::: t)) b'
              -> if Local v `Set.member` fvs b then
                prettyParens (d > 1) $ withIe (pretty v <+> colon <+> withPi (go i 0 t)) <+> arrow <+> go (succ i) 1 b
              else
                prettyParens (d > 1) $ withPi (go i 2 t <+> arrow <+> go (succ i) 1 b)
              where withPi
                      | ie == Ex, pi == More = id
                      | ie == Im, pi == Zero = id
                      | otherwise  = (pretty pi <+>)
                    withIe
                      | ie == Im  = prettyBraces True
                      | otherwise = prettyParens True
                    arrow = blue (pretty "->")
            (f ::: _) :$ sp -> prettyParens (d > 10 && not (null sp)) $ group (align (nest 2 (vsep (pretty f : map (go i 11) (toList sp)))))

instance Pretty Value where
  pretty = prettyPrec 0

instance FreeVariables QName Value where
  fvs = \case
    Type -> mempty
    Lam _ (Scope b) -> fvs b
    Pi _ _ t (Scope b) -> fvs t <> fvs b
    (v ::: _) :$ sp -> fvs v <> foldMap fvs sp

free :: Typed QName -> Value
free (q ::: t) = (Free q ::: t) :$ Nil

lam :: Typed Name -> Value -> Value
lam (n ::: t) b = Lam t (bind (Local n) b)

lams :: Foldable t => t (Typed Name) -> Value -> Value
lams names body = foldr lam body names

unlam :: Alternative m => Name -> Value -> m (Typed Name, Value)
unlam n (Lam t b) = pure (n ::: t, instantiate (free (Local n ::: t)) b)
unlam _ _         = empty

unlams :: Value -> (Stack (Typed Name), Value)
unlams value = intro 0 (Nil, value)
  where intro i (names, value) = case unlam (Gensym "" i) value of
          Just (name, body) -> intro (succ i) (names :> name, body)
          Nothing           -> (names, value)

pi :: Typed (Name, Plicity, Usage) -> Value -> Value
pi ((n, p, u) ::: t) b = Pi p u t (bind (Local n) b)

unpi :: Alternative m => Name -> Value -> m (Typed (Name, Plicity, Usage), Value)
unpi n (Pi p u t b) = pure ((n, p, u) ::: t, instantiate (free (Local n ::: t)) b)
unpi _ _            = empty

unpis :: Value -> (Stack (Typed (Name, Plicity, Usage)), Value)
unpis value = intro 0 (Nil, value)
  where intro i (names, value) = case unpi (Gensym "" i) value of
          Just (name, body) -> intro (succ i) (names :> name, body)
          Nothing           -> (names, value)

($$) :: Value -> Value -> Value
Lam _ b    $$ v = instantiate v b
Pi _ _ _ b $$ v = instantiate v b
n :$ vs    $$ v = n :$ (vs :> v)
f          $$ v = error ("illegal application of " <> show (plain (pretty f)) <> " to " <> show (plain (pretty v)))

($$*) :: Foldable t => Value -> t Value -> Value
v $$* sp = foldl' ($$) v sp


-- | Substitute occurrences of a 'QName' with a 'Value' within another 'Value'.
--
--   prop> subst (Local (Name a)) (free (Local (Name b))) (Lam ($$ free (Local (Name a)))) == Lam ($$ free (Local (Name b)))
subst :: QName -> Value -> Value -> Value
subst name image = instantiate image . bind name

generalizeType :: Value -> Value
generalizeType ty = foldr generalize ty (localNames (fvs ty))
  where generalize n = pi ((n, Im, Zero) ::: Type)

generalizeValue :: Value -> Value -> Value
generalizeValue ty = lams (fmap (\ ((n, _, _) ::: t) -> n ::: t) params)
  where (params, _) = unpis ty


type Type = Value

data Typed a = a ::: Type
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

typedTerm :: Typed a -> a
typedTerm (a ::: _) = a

typedType :: Typed a -> Type
typedType (_ ::: t) = t

infix 6 :::

instance Pretty a => Pretty (Typed a) where
  pretty (a ::: t) = pretty a <+> colon <+> pretty t

instance Pretty a => PrettyPrec (Typed a)


erase :: Term (Core.Core (Typed n) (Typed q)) a -> Term (Core.Core n q) a
erase = cata go
  where go (Core.Free (n ::: _))       ann = In (Core.Free n)       ann
        go (Core.Lam (n ::: _) b)      ann = In (Core.Lam n b)      ann
        go (f Core.:$ a)               ann = In (f Core.:$ a)       ann
        go Core.Type                   ann = In Core.Type           ann
        go (Core.Pi (n ::: _) p u t b) ann = In (Core.Pi n p u t b) ann


abstractLam :: Foldable t => t (Typed QName) -> Value -> Value
abstractLam = flip (foldr abstract)
  where abstract (n ::: t) = Lam t . bind n

abstractPi :: Foldable t => t (Typed QName) -> Value -> Value
abstractPi = flip (foldr abstract)
  where abstract (n ::: t) = Pi Im More t . bind n


-- | Bind occurrences of a 'Name' in a 'Value' term, producing a 'Scope' in which the 'Name' is bound.
bind :: QName -> Value -> Scope
bind name = Scope . substIn (\ i (h ::: t) -> (:$ Nil) . (::: t) $ case h of
  Bound j -> Bound j
  Free n  -> if name == n then Bound i else Free n)

-- | Substitute a 'Value' term for the free variable in a given 'Scope', producing a closed 'Value' term.
instantiate :: Value -> Scope -> Value
instantiate image (Scope b) = substIn (\ i (h ::: t) -> case h of
  Bound j -> if i == j then image else (Bound j ::: t) :$ Nil
  Free n  -> free (n ::: t)) b

substIn :: (Int -> Typed Head -> Value)
        -> Value
        -> Value
substIn var = go 0
  where go _ Type                 = Type
        go i (Lam    t (Scope b)) = Lam    (go i t) (Scope (go (succ i) b))
        go i (Pi p u t (Scope b)) = Pi p u (go i t) (Scope (go (succ i) b))
        go i ((head ::: t) :$ sp) = var i (head ::: go i t) $$* fmap (go i) sp
