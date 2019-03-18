{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections, TypeOperators #-}
module Path.Value where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Error
import           Control.Monad ((<=<), ap)
import           Data.Foldable (foldl', toList)
import qualified Data.Set as Set
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Stack as Stack
import           Path.Usage
import           Prelude hiding (pi)

data Value a
  = Type                                 -- ^ @'Type' : 'Type'@.
  | Lam                        (Scope a) -- ^ A lambda abstraction.
  | Pi Plicity Usage (Value a) (Scope a) -- ^ A ∏ type, with a 'Usage' annotation.
  | a :$ Stack (Value a)                 -- ^ A neutral term represented as a function on the right and a list of arguments to apply it.
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Value (Incr a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance PrettyPrec (Value Meta) where
  prettyPrec = prettyValue qlocal

instance PrettyPrec (Value Name) where
  prettyPrec = prettyValue Local

prettyValue :: (Ord name, Pretty name) => (Gensym -> name) -> Int -> Value name -> Doc
prettyValue localName d = run . runNaming (Root "pretty") . go d
  where go d = \case
          Lam b -> do
            (as, b') <- unlams localName (Lam b)
            b'' <- go 0 b'
            pure (prettyParens (d > 0) (align (group (cyan backslash <+> foldr (var (fvs b')) (linebreak <> cyan dot <+> b'') as))))
            where var vs n rest
                    | n `Set.member` vs = pretty n   <+> rest
                    | otherwise         = pretty '_' <+> rest
          Type -> pure (yellow (pretty "Type"))
          Pi ie pi t b -> do
            name <- gensym ""
            let b' = instantiate (pure (localName name)) b
            if ie == Im || localName name `Set.member` fvs b' then do
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
          f :$ sp -> do
            sp' <- traverse (go 11) (toList sp)
            pure (prettyParens (d > 10 && not (null sp)) ((group (align (nest 2 (vsep (pretty f : sp')))))))

instance Pretty (Value Meta) where
  pretty = prettyPrec 0

instance Pretty (Value Name) where
  pretty = prettyPrec 0

instance Ord a => FreeVariables a (Value a) where
  fvs = foldMap Set.singleton

instance Applicative Value where
  pure = (:$ Nil)
  (<*>) = ap

instance Monad Value where
  a >>= f = joinT (fmap f a)


lam :: Eq a => a -> Value a -> Value a
lam n b = Lam (bind n b)

lams :: (Eq a, Foldable t) => t a -> Value a -> Value a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Value a -> m (a, Value a)
unlam n (Lam b) = pure (n, instantiate (pure n) b)
unlam _ _       = empty

unlams :: (Carrier sig m, Member Naming sig) => (Gensym -> name) -> Value name -> m (Stack name, Value name)
unlams localName value = intro (Nil, value)
  where intro (names, value) = do
          name <- gensym ""
          case unlam (localName name) value of
            Just (name, body) -> intro (names :> name, body)
            Nothing           -> pure (names, value)

pi :: Eq a => (a, Plicity, Usage) ::: Type a -> Value a -> Value a
pi ((n, p, u) ::: t) b = Pi p u t (bind n b)

pis :: (Eq a, Foldable t) => t ((a, Plicity, Usage) ::: Type a) -> Value a -> Value a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Value a -> m ((a, Plicity, Usage) ::: Type a, Value a)
unpi n (Pi p u t b) = pure ((n, p, u) ::: t, instantiate (pure n) b)
unpi _ _            = empty

unpis :: (Carrier sig m, Member Naming sig) => (Gensym -> name) -> Value name -> m (Stack ((name, Plicity, Usage) ::: Type name), Value name)
unpis qlocal value = intro (Nil, value)
  where intro (names, value) = gensym "" >>= \ root -> case unpi (qlocal root) value of
          Just (name, body) -> intro (names :> name, body)
          Nothing           -> pure (names, value)

($$) :: Value a -> Value a -> Value a
Lam      b $$ v = instantiate v b
Pi _ _ _ b $$ v = instantiate v b
n :$ vs    $$ v = n :$ (vs :> v)
_          $$ _ = error "illegal application of Type"

($$*) :: Foldable t => Value a -> t (Value a) -> Value a
v $$* sp = foldl' ($$) v sp


gfoldT :: forall m n b
       .  (forall a . n (Incr a) -> n a)
       -> (forall a . m a -> Stack (n a) -> n a)
       -> (forall a . n a)
       -> (forall a . Plicity -> Usage -> n a -> n (Incr a) -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Value (m b)
       -> n b
gfoldT lam app ty pi dist = go
  where go :: Type (m x) -> n x
        go = \case
          Lam (Scope b) -> lam (go (dist <$> b))
          f :$ a -> app f (fmap go a)
          Type -> ty
          Pi p m t (Scope b) -> pi p m (go t) (go (dist <$> b))

joinT :: Value (Value a) -> Value a
joinT = gfoldT (Lam . Scope) ($$*) Type (\ p m t -> Pi p m t . Scope) (incr (pure Z) (fmap S))


-- | Substitute occurrences of a variable with a 'Value' within another 'Value'.
--
--   prop> substitute a (pure b) (Lam (Scope (pure (S a)))) === Lam (Scope (pure (S b)))
substitute :: Eq a => a -> Value a -> Value a -> Value a
substitute name image = instantiate image . bind name

generalizeType :: Value Meta -> Value Name
generalizeType ty = pis (foldMap f (fvs ty)) ty >>= \case { Name (Global n) -> pure (Global n) ; _ -> undefined }
  where f name
          | Name (Global (_ :.: _)) <- name = Set.empty
          | otherwise                       = Set.singleton ((name, Im, Zero) ::: Type)

generalizeValue :: (Carrier sig m, Member (Error Gensym) sig, Member Naming sig) => Value Meta ::: Type Name -> m (Value Name)
generalizeValue (value ::: ty) = strengthen <=< namespace "generalizeValue" $ do
  (names, _) <- unpis Local ty
  pure (lams (foldr (\case
    ((n, Im, _) ::: _) -> (Name n :)
    _                  -> id) [] names) value)


weaken :: Value Name -> Value Meta
weaken = fmap Name

strengthen :: (Carrier sig m, Member (Error Gensym) sig) => Value Meta -> m (Value Name)
strengthen = traverse $ \case
  Meta m -> throwError m
  Name (Global q) -> pure (Global q)
  Name (Local n) -> pure (Local n)


type Type = Value


-- | Bind occurrences of an 'Meta' in a 'Value' term, producing a 'Scope' in which the 'Meta' is bound.
bind :: Eq a => a -> Value a -> Scope a
bind name = Scope . fmap (match name)

-- | Substitute a 'Value' term for the free variable in a given 'Scope', producing a closed 'Value' term.
instantiate :: Value a -> Scope a -> Value a
instantiate t (Scope b) = b >>= subst t . fmap pure


-- $setup
-- >>> import Test.QuickCheck
