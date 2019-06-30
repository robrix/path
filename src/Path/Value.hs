{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TupleSections, TypeOperators #-}
module Path.Value where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.Reader hiding (Local)
import           Control.Monad (ap, unless)
import           Data.Coerce
import           Data.Foldable (foldl', toList)
import           Data.Functor.Identity
import qualified Data.Set as Set
import           Path.Name
import           Path.Plicity
import           Path.Pretty
import           Path.Stack as Stack
import           Path.Usage
import           Prelude hiding (pi)
import           Text.Trifecta.Rendering (Span)

data Value a
  = Type                                                  -- ^ @'Type' : 'Type'@.
  | Lam Plicity (Value (Incr (Value a)))                  -- ^ A lambda abstraction.
  | Pi (Plicit (Used (Value a))) (Value (Incr (Value a))) -- ^ A ∏ type, with a 'Usage' annotation.
  | Name a :$ Stack (Plicit (Value a))                    -- ^ A neutral term represented as a function and a 'Stack' of arguments to apply it to.
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

prettyValue :: (Carrier sig m, Member Naming sig) => Value Meta -> m Prec
prettyValue = go
  where go = \case
          Lam ie b -> do
            (as, b') <- un (orTerm (unlam . Name)) (Lam ie b)
            b'' <- go b'
            pure (prec 0 (align (group (cyan backslash <+> foldr (var (fvs b')) (linebreak <> cyan dot <+> prettyPrec 0 b'') as))))
            where var vs (p :< n) rest
                    | n `Set.member` vs = prettyPlicity False (p :< pretty (Local n)) <+> rest
                    | otherwise         = prettyPlicity False (p :< pretty '_')       <+> rest
          Type -> pure (atom (yellow (pretty "Type")))
          v@Pi{} -> do
            (pis, body) <- un (orTerm (\ n -> \case
              Pi (p :< u :@ t) b -> let b' = instantiate (pure (Name n)) b in Just ((p :< Name n ::: u :@ t, Name n `Set.member` fvs b'), b')
              _                    -> Nothing)) v
            pis' <- traverse (uncurry prettyPi) pis
            body' <- go body
            pure (prec 0 (encloseSep l mempty (flatAlt mempty space <> arrow <> space) (toList (pis' :> prettyPrec 1 body'))))
            where withPi Ex More = prettyPrec 1
                  withPi Im Zero = prettyPrec 1
                  withPi _  pi   = (pretty pi <+>) . prettyPrec 11
                  arrow = blue (pretty "->")
                  l = flatAlt (space <> space <> space) mempty
                  prettyPi (p :< n ::: u :@ t) isUsed = do
                    t' <- withPi p u <$> go t
                    pure $! prettyPlicity isUsed (p :< if isUsed then pretty (Local n ::: t') else t')
          f :$ sp -> do
            sp' <- traverse prettyArg (toList sp)
            pure (if null sp then
              atom (pretty f)
            else
              prec 10 (hsep (pretty f : sp')))
            where prettyArg (Im :< a) = prettyBraces True . prettyPrec 0 <$> go a
                  prettyArg (Ex :< a) = prettyPrec 11 <$> go a

instance Pretty (Value Meta) where
  pretty = prettyPrec 0 . run . runNaming (Root "pretty") . prettyValue

instance Pretty (Value Gensym) where
  pretty = pretty . fmap Name

instance Ord a => FreeVariables a (Value a) where
  fvs = foldMap Set.singleton

instance Applicative Value where
  pure = (:$ Nil) . Local
  (<*>) = ap

instance Monad Value where
  a >>= f = efold (name id global) Lam ($$*) Type Pi pure (f . runIdentity) (coerce a)


global :: Qualified -> Value a
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


efold :: forall l m n a b
      .  (forall a . Name (m a) -> n a)
      -> (forall a . Plicity -> n (Incr (n a)) -> n a)
      -> (forall a . n a -> Stack (Plicit (n a)) -> n a)
      -> (forall a . n a)
      -> (forall a . Plicit (Used (n a)) -> n (Incr (n a)) -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (l a -> m b)
      -> Value (l a)
      -> n b
efold var lam app ty pi k = go
  where go :: forall l' x y . (l' x -> m y) -> Value (l' x) -> n y
        go h = \case
          Type -> ty
          Lam p b -> lam p (go (k . fmap (go h)) b)
          f :$ a -> app (var (h <$> f)) (fmap (go h) <$> a)
          Pi t b -> pi (fmap (go h) <$> t) (go (k . fmap (go h)) b)


generalizeType :: Value Meta -> Value Gensym
generalizeType ty = unsafeStrengthen <$> pis (foldMap f (fvs ty)) ty
  where f name = Set.singleton (Im :< name ::: Zero :@ Type)


weaken :: Value Gensym -> Value Meta
weaken = fmap Name

strengthen :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => Value Meta -> m (Value Gensym)
strengthen ty = do
  let mvs = toList (metaNames (fvs ty))
  unless (null mvs) $ unsolvedMetavariables mvs ty
  pure (unsafeStrengthen <$> ty)

unsafeStrengthen :: Meta -> Gensym
unsafeStrengthen = \case { Name n -> n ; _ -> undefined }


unsolvedMetavariables :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => [Gensym] -> Value Meta -> m a
unsolvedMetavariables metas ty = do
  span <- ask
  throwError (prettyErr span (pretty "unsolved metavariable" <> (if length metas == 1 then mempty else pretty "s") <+> fillSep (punctuate comma (map (pretty . Meta) metas))) [pretty ty])


type Type = Value


-- $setup
-- >>> import Test.QuickCheck
