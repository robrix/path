{-# LANGUAGE DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, TupleSections #-}
module Path.Value where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Fresh
import           Control.Effect.Reader hiding (Local)
import           Data.Foldable (foldl', toList)
import qualified Data.Set as Set
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Stack as Stack
import           Path.Usage
import           Prelude hiding (pi)

data Value
  = Type                         -- ^ @'Type' : 'Type'@.
  | Lam              Value Scope -- ^ A lambda abstraction.
  | Pi Plicity Usage Value Scope -- ^ A ∏ type, with a 'Usage' annotation.
  | Typed Head :$ Stack Value    -- ^ A neutral term represented as a function on the right and a list of arguments to apply it.
  deriving (Eq, Ord, Show)

newtype Scope = Scope Value
  deriving (Eq, Ord, Pretty, PrettyPrec, Show)

instance PrettyPrec Value where
  prettyPrec d = run . runFresh . runReader (Root "pretty") . go d
    where go d = \case
            Lam t b -> do
              (as, b') <- unlamsM (Lam t b)
              b'' <- go 0 b'
              pure (prettyParens (d > 0) (align (group (cyan backslash <+> foldr (var (fvs b')) (line <> cyan dot <+> b'') as))))
              where var vs (n ::: _) rest
                      | Local n `Set.member` vs = pretty n   <+> rest
                      | otherwise               = pretty '_' <+> rest
            Type -> pure (yellow (pretty "Type"))
            Pi ie pi t b -> do
              name <- gensym ""
              let b' = instantiate (free (Local name ::: t)) b
              if Local name `Set.member` fvs b' then do
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

instance FreeVariables QName Value where
  fvs = \case
    Type -> mempty
    Lam _ (Scope b) -> fvs b
    Pi _ _ t (Scope b) -> fvs t <> fvs b
    (v ::: _) :$ sp -> fvs v <> foldMap fvs sp

free :: Typed QName -> Value
free (q ::: t) = (Free q ::: t) :$ Nil

lam :: Typed Gensym -> Value -> Value
lam (n ::: t) b = Lam t (bind (Local n) b)

lams :: Foldable t => t (Typed Gensym) -> Value -> Value
lams names body = foldr lam body names

unlam :: Alternative m => Gensym -> Value -> m (Typed Gensym, Value)
unlam n (Lam t b) = pure (n ::: t, instantiate (free (Local n ::: t)) b)
unlam _ _         = empty

unlams :: Gensym -> Value -> (Stack (Typed Gensym), Value)
unlams root value = intro (root // "unlams") (Nil, value)
  where intro root (names, value) = case unlam root value of
          Just (name, body) -> intro (prime root) (names :> name, body)
          Nothing           -> (names, value)

unlamsM :: (Carrier sig m, Member Fresh sig, Member (Reader Gensym) sig, Monad m) => Value -> m (Stack (Typed Gensym), Value)
unlamsM value = intro (Nil, value)
  where intro (names, value) = do
          name <- gensym ""
          case unlam name value of
            Just (name, body) -> intro (names :> name, body)
            Nothing           -> pure (names, value)

pi :: Typed (Gensym, Plicity, Usage) -> Value -> Value
pi ((n, p, u) ::: t) b = Pi p u t (bind (Local n) b)

pis :: Foldable t => t (Typed (Gensym, Plicity, Usage)) -> Value -> Value
pis names body = foldr pi body names

unpi :: Alternative m => Gensym -> Value -> m (Typed (Gensym, Plicity, Usage), Value)
unpi n (Pi p u t b) = pure ((n, p, u) ::: t, instantiate (free (Local n ::: t)) b)
unpi _ _            = empty

unpis :: Gensym -> Value -> (Stack (Typed (Gensym, Plicity, Usage)), Value)
unpis root value = intro (root // "unpis") (Nil, value)
  where intro root (names, value) = case unpi root value of
          Just (name, body) -> intro (prime root) (names :> name, body)
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
--   prop> subst (Local (Root a)) (free (Local (Root b))) (Lam ($$ free (Local (Root a)))) == Lam ($$ free (Local (Root b)))
subst :: QName -> Value -> Value -> Value
subst name image = instantiate image . bind name

generalizeType :: Value -> Value
generalizeType ty = pis (Set.map ((::: Type) . (, Im, Zero)) (localNames (fvs ty))) ty

generalizeValue :: Type -> Value -> Value
generalizeValue ty = lams (fmap (\ ((n, _, _) ::: t) -> n ::: t) params)
  where (params, _) = unpis (Root "generalizeValue") ty


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


abstractLam :: Foldable t => t (Typed QName) -> Value -> Value
abstractLam = flip (foldr abstract)
  where abstract (n ::: t) = Lam t . bind n


-- | Bind occurrences of a 'Gensym' in a 'Value' term, producing a 'Scope' in which the 'Name' is bound.
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
