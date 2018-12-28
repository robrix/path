{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Value where

import Data.Foldable (foldl', toList)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Path.Back as Back
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Usage

data Value a
  = Type                                       -- ^ @'Type' : 'Type'@.
  | Lam Name                         (Value a) -- ^ A lambda abstraction.
  | Pi  Name Plicity Usage (Value a) (Value a) -- ^ A ∏ type, with a 'Usage' annotation.
  | Back (Value a) :& a                        -- ^ A neutral term represented as a function on the right and a list of arguments to apply it to in reverse (i.e. &, not $) order.
  deriving (Eq, Ord, Show)

instance PrettyPrec (Value QName) where
  prettyPrec d = \case
    Type -> yellow (pretty "Type")
    Lam v b -> prettyParens (d > 0) $ align (group (cyan backslash <+> go v b))
      where go v b = var v b <> case b of
              Lam v' b' -> space <> go v' b'
              _         -> line <> cyan dot <+> prettyPrec 0 b
            var v b | Local v `Set.member` fvs b = pretty v
                    | otherwise                  = pretty '_'
    Nil :& f -> pretty f
    as :& f -> prettyParens (d > 10) $ group (nest 2 (pretty f </> align (vsep (map (prettyPrec 11) (toList as)))))
    Pi v ie pi t b
      | Local v `Set.member` fvs b -> case pi of
        Zero -> prettyParens (d > 1) $ align (group (cyan (pretty "∀") <+> pretty v <+> colon <+> prettyPrec 2 t <> line <> cyan dot <+> prettyPrec 1 b))
        _    -> prettyParens (d > 1) $ withIe (pretty v <+> colon <+> withPi (prettyPrec 0 t)) <+> arrow <+> prettyPrec 1 b
      | otherwise                  -> prettyParens (d > 1) $ withPi (prettyPrec 2 t <+> arrow <+> prettyPrec 1 b)
      where withPi
              | pi == More = id
              | otherwise  = (pretty pi <+>)
            withIe
              | ie == Im  = prettyBraces True
              | otherwise = prettyParens True
            arrow = blue (pretty "->")

instance Pretty (Value QName) where
  pretty = prettyPrec 0

instance FreeVariables QName (Value QName) where
  fvs = \case
    Type -> mempty
    Lam v b -> Set.delete (Local v) (fvs b)
    Pi v _ _ t b -> fvs t <> Set.delete (Local v) (fvs b)
    a :& f -> foldMap fvs a <> Set.singleton f

vfree :: a -> Value a
vfree = (Nil :&)

vapp :: Value QName -> Value QName -> Value QName
vapp (Lam n b) v = subst (Local n) v b
vapp (Pi n _ _ _ b) v = subst (Local n) v b
vapp (vs :& n) v = (vs :> v) :& n
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)

-- | Capture-avoiding substitution.
subst :: QName -> Value QName -> Value QName -> Value QName
subst for rep = go 0
  where fvsRep = fvs rep
        go i = \case
          Type -> Type
          Lam v b
            | for == Local v -> Lam v b
            | Local v `Set.member` fvsRep
            , let new = gensym i (fvs b)
            -> Lam new (go (succ i) (subst (Local v) (vfree (Local new)) b))
            | otherwise      -> Lam v (go i b)
          Pi v p u t b
            | for == Local v -> Pi v p u (go i t) b
            | Local v `Set.member` fvsRep
            , let new = gensym i (fvs b)
            -> Pi new p u (go i t) (go (succ i) (subst (Local v) (vfree (Local new)) b))
            | otherwise -> Pi v p u (go i t) (go i b)
          a :& v
            | for == v  -> foldl' app rep a
            | otherwise -> fmap (go i) a :& v
            where app f a = f `vapp` go i a
        locals = foldMap (\case { Local (Gensym i) -> Set.singleton i ; _ -> mempty })
        gensym i names = Gensym (maybe i (succ . fst) (Set.maxView (locals (names <> fvsRep))))


aeq :: Value QName -> Value QName -> Bool
aeq = go (0 :: Int) [] []
  where go i env1 env2 v1 v2 = case (v1, v2) of
          (Type,              Type)              -> True
          (Lam n1 b1,         Lam n2 b2)         -> go (succ i) ((Local n1, i) : env1) ((Local n2, i) : env2) b1 b2
          (Pi n1 p1 e1 t1 b1, Pi n2 p2 e2 t2 b2) -> p1 == p2 && e1 == e2 && go i env1 env2 t1 t2 && go (succ i) ((Local n1, i) : env1) ((Local n2, i) : env2) b1 b2
          (as1 :& n1,         as2 :& n2)         -> fromMaybe (n1 == n2) ((==) <$> Prelude.lookup n1 env1 <*> Prelude.lookup n2 env2) && length as1 == length as2 && and (Back.zipWith (go i env1 env2) as1 as2)
          _                                      -> False
