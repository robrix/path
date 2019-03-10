{-# LANGUAGE DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, TupleSections, TypeOperators #-}
module Path.Value where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Fresh
import           Control.Effect.Reader hiding (Local)
import           Data.Bifunctor
import           Data.Foldable (foldl', toList)
import qualified Data.Set as Set
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Stack as Stack
import           Path.Usage
import           Prelude hiding (pi)

data Value
  = Type                                 -- ^ @'Type' : 'Type'@.
  | Lam              Value Scope         -- ^ A lambda abstraction.
  | Pi Plicity Usage Value Scope         -- ^ A ∏ type, with a 'Usage' annotation.
  | (Head MName ::: Type) :$ Stack Value -- ^ A neutral term represented as a function on the right and a list of arguments to apply it.
  deriving (Eq, Ord, Show)

newtype Scope = Scope Value
  deriving (Eq, Ord, Pretty, PrettyPrec, Show)

instance PrettyPrec Value where
  prettyPrec d = run . runFresh . runReader (Root "pretty") . go d
    where go d = \case
            Lam t b -> do
              (as, b') <- unlams (Lam t b)
              b'' <- go 0 b'
              pure (prettyParens (d > 0) (align (group (cyan backslash <+> foldr (var (fvs b')) (line <> cyan dot <+> b'') as))))
              where var vs (n ::: _) rest
                      | n `Set.member` vs = pretty n   <+> rest
                      | otherwise         = pretty '_' <+> rest
            Type -> pure (yellow (pretty "Type"))
            Pi ie pi t b -> do
              name <- gensym ""
              let b' = instantiate (free (qlocal name ::: t)) b
              if qlocal name `Set.member` fvs b' then do
                t' <- go 0 t
                b'' <- go 1 b'
                pure (prettyParens (d > 1) (withIe (pretty name <+> colon <+> withPi t') <+> arrow <+> b''))
              else do
                t' <- go 2 t
                b'' <- go 1 b'
                pure (prettyParens (d > 1) (withPi (t' <+> arrow <+> b'')))
              where withPi
                      | ie == Ex, pi == More = id
                      | ie == Im, pi == Zero = id
                      | otherwise  = (pretty pi <+>)
                    withIe
                      | ie == Im  = prettyBraces True
                      | otherwise = prettyParens True
                    arrow = blue (pretty "->")
            (f ::: _) :$ sp -> do
              sp' <- traverse (go 11) (toList sp)
              pure (prettyParens (d > 10 && not (null sp)) ((group (align (nest 2 (vsep (pretty f : sp')))))))

instance Pretty Value where
  pretty = prettyPrec 0

instance FreeVariables MName Value where
  fvs = \case
    Type -> mempty
    Lam _ (Scope b) -> fvs b
    Pi _ _ t (Scope b) -> fvs t <> fvs b
    (v ::: _) :$ sp -> fvs v <> foldMap fvs sp

free :: MName ::: Type -> Value
free (q ::: t) = (Free q ::: t) :$ Nil

lam :: MName ::: Type -> Value -> Value
lam (n ::: t) b = Lam t (bind n b)

lams :: Foldable t => t (MName ::: Type) -> Value -> Value
lams names body = foldr lam body names

unlam :: Alternative m => MName -> Value -> m (MName ::: Type, Value)
unlam n (Lam t b) = pure (n ::: t, instantiate (free (n ::: t)) b)
unlam _ _         = empty

unlams :: (Carrier sig m, Member Fresh sig, Member (Reader Gensym) sig) => Value -> m (Stack (MName ::: Type), Value)
unlams value = intro (Nil, value)
  where intro (names, value) = do
          name <- gensym ""
          case unlam (qlocal name) value of
            Just (name, body) -> intro (names :> name, body)
            Nothing           -> pure (names, value)

pi :: (MName, Plicity, Usage) ::: Type -> Value -> Value
pi ((n, p, u) ::: t) b = Pi p u t (bind n b)

pis :: Foldable t => t ((MName, Plicity, Usage) ::: Type) -> Value -> Value
pis names body = foldr pi body names

unpi :: Alternative m => MName -> Value -> m ((MName, Plicity, Usage) ::: Type, Value)
unpi n (Pi p u t b) = pure ((n, p, u) ::: t, instantiate (free (n ::: t)) b)
unpi _ _            = empty

unpis :: (Carrier sig m, Member Fresh sig, Member (Reader Gensym) sig) => Value -> m (Stack ((MName, Plicity, Usage) ::: Type), Value)
unpis value = intro (Nil, value)
  where intro (names, value) = gensym "" >>= \ root -> case unpi (qlocal root) value of
          Just (name, body) -> intro (names :> name, body)
          Nothing           -> pure (names, value)

($$) :: Value -> Value -> Value
Lam _ b    $$ v = instantiate v b
Pi _ _ _ b $$ v = instantiate v b
n :$ vs    $$ v = n :$ (vs :> v)
_          $$ _ = error "illegal application of Type"

($$*) :: Foldable t => Value -> t Value -> Value
v $$* sp = foldl' ($$) v sp


-- | Substitute occurrences of an 'MName' with a 'Value' within another 'Value'.
--
--   prop> subst (Local (Root a)) (free (Local (Root b))) (Lam ($$ free (Local (Root a)))) == Lam ($$ free (Local (Root b)))
subst :: MName -> Value -> Value -> Value
subst name image = instantiate image . bind name

generalizeType :: Value -> Value
generalizeType ty = pis (Set.map ((::: Type) . (, Im, Zero) . qlocal) (localNames (fvs ty))) ty

generalizeValue :: (Carrier sig m, Effect sig, Member (Reader Gensym) sig) => Type -> Value -> m Value
generalizeValue ty value = runFresh . local (// "generalizeValue") $ do
  (names, _) <- unpis ty
  pure (lams (fmap (\ ((n, _, _) ::: t) -> n ::: t) names) value)


type Type = Value

data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifunctor (:::) where
  bimap f g (a ::: b) = f a ::: g b

typedTerm :: a ::: b -> a
typedTerm (a ::: _) = a

typedType :: a ::: b -> b
typedType (_ ::: t) = t

infix 6 :::

instance (Pretty a, Pretty b) => Pretty (a ::: b) where
  pretty (a ::: t) = pretty a <+> colon <+> pretty t

instance (Pretty a, Pretty b) => PrettyPrec (a ::: b)


-- | Bind occurrences of an 'MName' in a 'Value' term, producing a 'Scope' in which the 'MName' is bound.
bind :: MName -> Value -> Scope
bind name = Scope . substIn (\ i (h ::: t) -> (:$ Nil) . (::: t) $ case h of
  Bound j -> Bound j
  Free n  -> if name == n then Bound i else Free n)

-- | Substitute a 'Value' term for the free variable in a given 'Scope', producing a closed 'Value' term.
instantiate :: Value -> Scope -> Value
instantiate image (Scope b) = substIn (\ i (h ::: t) -> case h of
  Bound j -> if i == j then image else (Bound j ::: t) :$ Nil
  Free n  -> free (n ::: t)) b

substIn :: (Int -> Head MName ::: Type -> Value)
        -> Value
        -> Value
substIn var = go 0
  where go _ Type                 = Type
        go i (Lam    t (Scope b)) = Lam    (go i t) (Scope (go (succ i) b))
        go i (Pi p u t (Scope b)) = Pi p u (go i t) (Scope (go (succ i) b))
        go i ((head ::: t) :$ sp) = var i (head ::: go i t) $$* fmap (go i) sp
