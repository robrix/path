{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections, TypeOperators #-}
module Path.Value where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.Reader hiding (Local)
import           Control.Monad (ap, unless)
import           Data.Foldable (foldl', toList)
import qualified Data.Set as Set
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Stack as Stack
import           Path.Usage
import           Prelude hiding (pi)
import           Text.Trifecta.Rendering (Span)

data Value a
  = Lam Plicity (Scope Value a)                  -- ^ A lambda abstraction.
  | a :$ Stack (Plicit (Value a))                -- ^ A neutral term represented as a function and a 'Stack' of arguments to apply it to.
  | Type                                         -- ^ @'Type' : 'Type'@.
  | Pi (Plicit (Used (Value a))) (Scope Value a) -- ^ A ∏ type, with a 'Usage' annotation.
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

prettyValue :: (Carrier sig m, Member Naming sig) => Value (Name Meta) -> m (Prec Doc)
prettyValue = go
  where go :: (Carrier sig m, Member Naming sig) => Value (Name Meta) -> m (Prec Doc)
        go = \case
          Lam ie b -> do
            (as, b') <- un (orTerm (unlam . Local . Name)) (Lam ie b)
            b'' <- go b'
            pure (prec 0 (align (group (cyan backslash <+> foldr (var (fvs b')) (linebreak <> cyan dot <+> prettyPrec 0 b'') as))))
            where var vs (p :< n) rest
                    | n `Set.member` vs = prettyPlicity False (p :< pretty (Local n)) <+> rest
                    | otherwise         = prettyPlicity False (p :< pretty '_')       <+> rest
          f :$ sp -> do
            sp' <- traverse prettyArg (toList sp)
            pure (if null sp then
              atom (pretty f)
            else
              prec 10 (hsep (pretty f : sp')))
            where prettyArg (Im :< a) = prettyBraces True . prettyPrec 0 <$> go a
                  prettyArg (Ex :< a) = prettyPrec 11 <$> go a
          Type -> pure (atom (yellow (pretty "Type")))
          v@Pi{} -> do
            (pis, body) <- un (orTerm (\ n -> \case
              Pi (p :< u :@ t) b -> let b' = instantiate (pure (Local (Name n))) b in Just ((p :< Local (Name n) ::: u :@ t, Local (Name n) `Set.member` fvs b'), b')
              _                  -> Nothing)) v
            pis' <- traverse (uncurry prettyPi) pis
            body' <- go body
            pure (prec 0 (encloseSep l mempty (flatAlt mempty space <> arrow <> space) (toList (pis' :> prettyPrec 1 body'))))
            where withPi (Ex :< More :@ t) =                   prettyPrec 1  <$> go t
                  withPi (Im :< Zero :@ t) =                   prettyPrec 1  <$> go t
                  withPi (_  :< pi   :@ t) = (pretty pi <+>) . prettyPrec 11 <$> go t
                  arrow = blue (pretty "->")
                  l = flatAlt (space <> space <> space) mempty
                  prettyPi (p :< n ::: t) isUsed = do
                    t' <- withPi (p :< t)
                    pure $! prettyPlicity isUsed (p :< if isUsed then pretty (Local n ::: t') else t')

instance Pretty (Value (Name Meta)) where
  pretty = prettyPrec 0 . run . runNaming . prettyValue

instance Pretty (Value (Name Gensym)) where
  pretty = pretty . weaken

instance Ord a => FreeVariables a (Value a) where
  fvs = foldMap Set.singleton

instance Applicative Value where
  pure = (:$ Nil)
  (<*>) = ap

instance Monad Value where
  a >>= f = eiter id embed pure f a


data ValueF f a
  = LamF Plicity (Scope f a)              -- ^ A lambda abstraction.
  | f a :$$ Stack (Plicit (f a))          -- ^ A neutral term represented as a function and a 'Stack' of arguments to apply it to.
  | TypeF                                 -- ^ @'Type' : 'Type'@.
  | PiF (Plicit (Used (f a))) (Scope f a) -- ^ A ∏ type, with a 'Usage' annotation.
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (ValueF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (ValueF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (ValueF f a)

project :: Value a -> ValueF Value a
project (Lam p b) = LamF p b
project (f :$ a) = (f :$ Nil) :$$ a
project Type = TypeF
project (Pi t b) = PiF t b

embed :: ValueF Value a -> Value a
embed (LamF p b) = Lam p b
embed (f :$$ a) = f $$* a
embed TypeF = Type
embed (PiF t b) = Pi t b


global :: Qualified -> Value (Name a)
global = (:$ Nil) . Global

lam :: Eq a => Plicit a -> Value a -> Value a
lam (pl :< n) b = Lam pl (bind n b)

lams :: (Eq a, Foldable t) => t (Plicit a) -> Value a -> Value a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Value a -> m (Plicit a, Value a)
unlam n (Lam p b) = pure (p :< n, instantiate (pure n) b)
unlam _ _         = empty

pi :: Eq a => Plicit (a ::: Used (Type a)) -> Value a -> Value a
pi (p :< n ::: t) b = Pi (p :< t) (bind n b)

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t) => t (Plicit (a ::: Used (Type a))) -> Value a -> Value a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Value a -> m (Plicit (a ::: Used (Type a)), Value a)
unpi n (Pi (p :< t) b) = pure (p :< n ::: t, instantiate (pure n) b)
unpi _ _               = empty

($$) :: Value a -> Plicit (Value a) -> Value a
Lam _ b $$ (_ :< v) = instantiate v b
Pi _  b $$ (_ :< v) = instantiate v b
n :$ vs $$ v        = n :$ (vs :> v)
_       $$ _        = error "illegal application of Type"

($$*) :: Foldable t => Value a -> t (Plicit (Value a)) -> Value a
v $$* sp = foldl' ($$) v sp


eiter :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . ValueF n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (a -> m b)
      -> Value a
      -> n b
eiter var alg k = go
  where go :: forall x y . (x -> m y) -> Value x -> n y
        go h = \case
          Lam p b -> alg (LamF p (foldScope k go h b))
          f :$ a -> alg (var (h f) :$$ (fmap (go h) <$> a))
          Type -> alg TypeF
          Pi t b -> alg (PiF (fmap (go h) <$> t) (foldScope k go h b))


generalizeType :: Value (Name Meta) -> Value (Name Gensym)
generalizeType ty = fmap unsafeStrengthen <$> pis (foldMap f (fvs ty)) ty
  where f (Local name) = Set.singleton (Im :< Local name ::: Zero :@ Type)
        f _            = Set.empty


weaken :: Value (Name Gensym) -> Value (Name Meta)
weaken = fmap (fmap Name)

strengthen :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => Value (Name Meta) -> m (Value (Name Gensym))
strengthen ty = do
  let mvs = toList (metaNames (localNames (fvs ty)))
  unless (null mvs) $ unsolvedMetavariables mvs ty
  pure (fmap unsafeStrengthen <$> ty)

unsafeStrengthen :: Meta -> Gensym
unsafeStrengthen = \case { Name n -> n ; _ -> undefined }


unsolvedMetavariables :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => [Gensym] -> Value (Name Meta) -> m a
unsolvedMetavariables metas ty = do
  span <- ask
  throwError (prettyErr span (pretty "unsolved metavariable" <> (if length metas == 1 then mempty else pretty "s") <+> fillSep (punctuate comma (map (pretty . Meta) metas))) [pretty ty])


type Type = Value


-- $setup
-- >>> import Test.QuickCheck
