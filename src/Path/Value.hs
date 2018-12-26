{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Value where

import Data.Foldable (foldl', toList)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Path.Back as Back
import Path.Name
import Path.Pretty
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Value
  = Type                       -- ^ @'Type' : 'Type'@.
  | Lam Name             Value -- ^ A lambda abstraction.
  | Pi  Name Usage Value Value -- ^ A ∏ type, with a 'Usage' annotation.
  | Neutral (Back Value) QName -- ^ A neutral term represented as a function on the right and a list of arguments to apply it to in reverse (i.e. &, not $) order.
  deriving (Eq, Ord, Show)

instance PrettyPrec Value where
  prettyPrec d = \case
    Type -> yellow (pretty "Type")
    Lam v b -> prettyParens (d > 0) $ align (group (cyan backslash <+> go v b))
      where go v b = var v b <> case b of
              Lam v' b' -> space <> go v' b'
              _         -> line <> cyan dot <+> prettyPrec 0 b
            var v b | Local v `Set.member` fvs b = pretty v
                    | otherwise                  = pretty '_'
    Neutral Nil f -> pretty f
    Neutral as f -> prettyParens (d > 10) $ group (nest 2 (pretty f </> align (vsep (map (prettyPrec 11) (toList as)))))
    Pi v pi t b
      | Local v `Set.member` fvs b -> case pi of
        Zero -> prettyParens (d > 1) $ align (group (cyan (pretty "∀") <+> pretty v <+> colon <+> prettyPrec 2 t <> line <> cyan dot <+> prettyPrec 1 b))
        _    -> prettyParens (d > 1) $ prettyBraces True (pretty v <+> colon <+> withPi (prettyPrec 0 t)) <+> arrow <+> prettyPrec 1 b
      | otherwise                  -> prettyParens (d > 1) $ withPi (prettyPrec 2 t <+> arrow <+> prettyPrec 1 b)
      where withPi
              | pi == More = id
              | otherwise  = (pretty pi <+>)
            arrow = blue (pretty "->")

instance Pretty Value where
  pretty = prettyPrec 0

instance FreeVariables QName Value where
  fvs = \case
    Type -> mempty
    Lam v b -> Set.delete (Local v) (fvs b)
    Pi v _ t b -> fvs t <> Set.delete (Local v) (fvs b)
    Neutral a f -> foldMap fvs a <> Set.singleton f

vfree :: QName -> Value
vfree = Neutral Nil

vapp :: Value -> Value -> Value
vapp (Lam n b) v = subst (Local n) v b
vapp (Neutral vs n) v = Neutral (vs :> v) n
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)

-- | Capture-avoiding substitution.
subst :: QName -> Value -> Value -> Value
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
          Pi v u t b
            | for == Local v -> Pi v u (go i t) b
            | Local v `Set.member` fvsRep
            , let new = gensym i (fvs b)
            -> Pi new u (go i t) (go (succ i) (subst (Local v) (vfree (Local new)) b))
            | otherwise -> Pi v u (go i t) (go i b)
          Neutral a v
            | for == v  -> foldl' app rep a
            | otherwise -> Neutral (fmap (go i) a) v
            where app f a = f `vapp` go i a
        locals = foldMap (\case { Local (Gensym i) -> Set.singleton i ; _ -> Set.empty })
        gensym i names = Gensym (maybe i (succ . fst) (Set.maxView (locals (names <> fvsRep))))


aeq :: Value -> Value -> Bool
aeq = go (0 :: Int) [] []
  where go i env1 env2 v1 v2 = case (v1, v2) of
          (Type,           Type)           -> True
          (Lam n1 b1,      Lam n2 b2)      -> go (succ i) ((Local n1, i) : env1) ((Local n2, i) : env2) b1 b2
          (Pi n1 e1 t1 b1, Pi n2 e2 t2 b2) -> e1 == e2 && go i env1 env2 t1 t2 && go (succ i) ((Local n1, i) : env1) ((Local n2, i) : env2) b1 b2
          (Neutral as1 n1, Neutral as2 n2) -> fromMaybe (n1 == n2) ((==) <$> Prelude.lookup n1 env1 <*> Prelude.lookup n2 env2) && length as1 == length as2 && and (Back.zipWith (go i env1 env2) as1 as2)
          _                                -> False
