{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections, TypeOperators #-}
module Path.Value where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.Reader hiding (Local)
import           Control.Monad ((<=<), ap)
import           Data.Foldable (foldl', toList)
import qualified Data.Set as Set
import           Data.Traversable (for)
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Stack as Stack
import           Path.Usage
import           Prelude hiding (pi)
import           Text.Trifecta.Rendering (Span)

data Value a
  = Type                                   -- ^ @'Type' : 'Type'@.
  | Lam Plicity                  (Scope a) -- ^ A lambda abstraction.
  | Pi (Plicit (Usage, Value a)) (Scope a) -- ^ A ∏ type, with a 'Usage' annotation.
  | a :$ Stack (Plicit (Value a))          -- ^ A neutral term represented as a function on the right and a list of arguments to apply it.
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Value (Incr a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

prettyValue :: (Carrier sig m, Ord name, Pretty name, Member Naming sig) => (Gensym -> name) -> Value name -> m Prec
prettyValue localName = go
  where go = \case
          Lam ie b -> do
            (as, b') <- unlams localName (Lam ie b)
            b'' <- go b'
            pure (prec 0 (align (group (cyan backslash <+> foldr (var (fvs b')) (linebreak <> cyan dot <+> prettyPrec 0 b'') as))))
            where var vs (p :< n) rest
                    | n `Set.member` vs = prettyPlicity False (p :< pretty n)   <+> rest
                    | otherwise         = prettyPlicity False (p :< pretty '_') <+> rest
          Type -> pure (atom (yellow (pretty "Type")))
          v@Pi{} -> do
            (pis, body) <- unpis localName v
            body' <- go body
            pis' <- traverse prettyPi pis
            pure (prec 0 (encloseSep l mempty (flatAlt mempty space <> arrow <> space) (toList (pis' :> prettyPrec 1 body'))))
            where withPi Ex More = prettyPrec 0
                  withPi Im Zero = prettyPrec 0
                  withPi _  pi   = (pretty pi <+>) . prettyPrec 11
                  arrow = blue (pretty "->")
                  l = flatAlt (space <> space <> space) mempty
                  prettyPi (p :< (n, u) ::: t) = do
                    t' <- go t
                    pure (pretty (p :< pretty (pretty n ::: withPi p u t')))
          f :$ sp -> do
            sp' <- traverse prettyArg (toList sp)
            pure (if null sp then
              atom (pretty f)
            else
              prec 10 (hsep (pretty f : sp')))
            where prettyArg (Im :< a) = prettyBraces True . prettyPrec 0 <$> go a
                  prettyArg (Ex :< a) = prettyPrec 11 <$> go a

instance Pretty (Value Meta) where
  pretty = prettyPrec 0 . run . runNaming (Root "pretty") . prettyValue qlocal

instance Pretty (Value Name) where
  pretty = prettyPrec 0 . run . runNaming (Root "pretty") . prettyValue Local

instance Ord a => FreeVariables a (Value a) where
  fvs = foldMap Set.singleton

instance Applicative Value where
  pure = (:$ Nil)
  (<*>) = ap

instance Monad Value where
  a >>= f = joinT (fmap f a)


un :: (Carrier sig m, Member Naming sig) => (Gensym -> Value name -> Maybe (a, Value name)) -> Value name -> m (Stack a, Value name)
un from = go Nil
  where go names value = do
          name <- gensym ""
          case from name value of
            Just (name, body) -> go (names :> name) body
            Nothing           -> pure (names, value)


lam :: Eq a => Plicit a -> Value a -> Value a
lam (pl :< n) b = Lam pl (bind n b)

lams :: (Eq a, Foldable t) => t (Plicit a) -> Value a -> Value a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Value a -> m (Plicit a, Value a)
unlam n (Lam p b) = pure (p :< n, instantiate (pure n) b)
unlam _ _         = empty

unlams :: (Carrier sig m, Member Naming sig) => (Gensym -> name) -> Value name -> m (Stack (Plicit name), Value name)
unlams localName = un (unlam . localName)

pi :: Eq a => Plicit (a, Usage) ::: Type a -> Value a -> Value a
pi (p :< (n, u) ::: t) b = Pi (p :< (u, t)) (bind n b)

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t) => t (Plicit (a, Usage) ::: Type a) -> Value a -> Value a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Value a -> m (Plicit (a, Usage) ::: Type a, Value a)
unpi n (Pi (p :< (u, t)) b) = pure (p :< (n, u) ::: t, instantiate (pure n) b)
unpi _ _                    = empty

unpis :: (Carrier sig m, Member Naming sig) => (Gensym -> name) -> Value name -> m (Stack (Plicit (name, Usage) ::: Type name), Value name)
unpis localName = un (unpi . localName)

($$) :: Value a -> Plicit (Value a) -> Value a
Lam _ b $$ (_ :< v) = instantiate v b
Pi  _ b $$ (_ :< v) = instantiate v b
n :$ vs $$ v        = n :$ (vs :> v)
_       $$ _        = error "illegal application of Type"

($$*) :: Foldable t => Value a -> t (Plicit (Value a)) -> Value a
v $$* sp = foldl' ($$) v sp


gfoldT :: forall m n b
       .  (forall a . Plicity -> n (Incr a) -> n a)
       -> (forall a . m a -> Stack (Plicit (n a)) -> n a)
       -> (forall a . n a)
       -> (forall a . Plicit (Usage, n a) -> n (Incr a) -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Value (m b)
       -> n b
gfoldT lam app ty pi dist = go
  where go :: Type (m x) -> n x
        go = \case
          Lam p (Scope b) -> lam p (go (dist <$> b))
          f :$ a -> app f (fmap (fmap go) a)
          Type -> ty
          Pi (p :< (m, t)) (Scope b) -> pi (p :< (m, go t)) (go (dist <$> b))

joinT :: Value (Value a) -> Value a
joinT = gfoldT (\ p -> Lam p . Scope) ($$*) Type (\ p -> Pi p . Scope) (incr (pure Z) (fmap S))


-- | Substitute occurrences of a variable with a 'Value' within another 'Value'.
--
--   prop> substitute a (pure b) (Lam (Scope (pure (S a)))) === Lam (Scope (pure (S b)))
substitute :: Eq a => a -> Value a -> Value a -> Value a
substitute name image = instantiate image . bind name

generalizeType :: Value Meta -> Value Name
generalizeType ty = pis (foldMap f (fvs ty)) ty >>= \case { Name (Global n) -> pure (Global n) ; _ -> undefined }
  where f name
          | Name (Global (_ :.: _)) <- name = Set.empty
          | otherwise                       = Set.singleton (Im :< (name, Zero) ::: Type)

generalizeValue :: (Carrier sig m, Member (Error Doc) sig, Member Naming sig, Member (Reader Span) sig) => Value Meta ::: Type Name -> m (Value Name)
generalizeValue (value ::: ty) = strengthen <=< namespace "generalizeValue" $ do
  (names, _) <- unpis Local ty
  pure (lams (foldr (\case
    Im :< (n, _) ::: _ -> ((Im :< Name n) :)
    _                  -> id) [] names) value)


weaken :: Value Name -> Value Meta
weaken = fmap Name

strengthen :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => Value Meta -> m (Value Name)
strengthen ty = for ty $ \case
  Meta m -> unsolvedMetavariable m ty
  Name (Global q) -> pure (Global q)
  Name (Local n) -> pure (Local n)


unsolvedMetavariable :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => Gensym -> Value Meta -> m a
unsolvedMetavariable meta ty = do
  span <- ask
  throwError (prettyErr span (pretty "unsolved metavariable" <+> squotes (pretty (Meta meta)) <+> pretty "in type" <+> pretty ty) [])


type Type = Value


-- | Bind occurrences of an 'Meta' in a 'Value' term, producing a 'Scope' in which the 'Meta' is bound.
bind :: Eq a => a -> Value a -> Scope a
bind name = Scope . fmap (match name)

-- | Substitute a 'Value' term for the free variable in a given 'Scope', producing a closed 'Value' term.
instantiate :: Value a -> Scope a -> Value a
instantiate t (Scope b) = b >>= subst t . fmap pure


-- $setup
-- >>> import Test.QuickCheck
