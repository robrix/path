{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Problem where

import           Control.Applicative (Alternative (..), Const (..))
import           Control.Effect.Carrier
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.Writer
import           Control.Monad.Module
import qualified Data.Set as Set
import           GHC.Generics (Generic1)
import           Path.Core
import           Path.Name
import           Path.Pretty
import           Path.Scope
import           Path.Stack as Stack
import           Path.Syntax
import           Path.Term
import           Prelude hiding (pi)

newtype P = P { unP :: Int }
  deriving (Eq, Ord, Show)

instance Pretty (Term (Problem :+: Core) Qualified) where
  pretty = snd . run . runWriter @(Set.Set Meta) . runReader (Nil @Meta) . runReader (P 0) . kcata id alg k (var . Global)
    where var (Global v) = pure (pretty (Global @Meta v))
          var (Local  v) = pretty v <$ tell (Set.singleton @Meta v)
          alg = \case
            R c -> case c of
              Lam (Scope b) -> do
                (n, b') <- bind Name (withPrec 0 b)
                prec 0 (pretty (cyan backslash) <+> pretty n </> cyan dot <+> b')
              f :$ a -> do
                f' <- withPrec 10 f
                a' <- withPrec 11 a
                prec 10 (f' <+> a')
              Let v (Scope b) -> do
                v' <- withPrec 0 v
                (n, b') <- bind Meta (withPrec 0 b)
                prec 0 (magenta (pretty "let") <+> pretty (n := v') </> magenta dot <+> b')
              Type -> pure (yellow (pretty "Type"))
              Pi t (Scope b) -> do
                t' <- withPrec 1 t
                (fvs, (n, b')) <- listen (bind Name (withPrec 0 b))
                let t'' | n `Set.member` fvs = parens (pretty (n ::: t'))
                        | otherwise          = t'
                prec 0 (t'' </> arrow <+> b')
            L p -> case p of
              Ex t (Scope b) -> do
                t' <- withPrec 1 t
                (n, b') <- bind Meta (withPrec 0 b)
                prec 0 (magenta (pretty "∃") <+> pretty (n ::: t') </> magenta dot <+> b')
              p1 :===: p2 -> do
                p1' <- withPrec 1 p1
                p2' <- withPrec 1 p2
                prec 0 (flatAlt (p1' <+> eq' <+> p2') (align (space <+> p1' </> eq' <+> p2')))
          arrow = blue (pretty "→")
          eq' = magenta (pretty "≡")
          k (Z ()) = ask >>= var . Local . Stack.head
          k (S n)  = local (Stack.tail @Meta) n
          prec d' doc = do
            d <- ask
            pure (prettyParens (d > P d') doc)
          withPrec i = local (const (P i)) . getConst
          bind cons m = do
            ns <- ask
            let n = cons $ case ns of
                  _ :> Meta sym -> prime sym
                  _ :> Name sym -> prime sym
                  _ -> Gensym Nil 0
            (,) n <$> censor (Set.delete n) (local (:> n) m)


-- FIXME: represent errors explicitly in the tree
-- FIXME: represent spans explicitly in the tree
data Problem f a
  = Ex (f a) (Scope () f a)
  | f a :===: f a
  deriving (Foldable, Functor, Generic1, HFunctor, Traversable)

infix 3 :===:

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Problem f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Problem f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (Problem f a)

instance HRModule Problem where
  Ex t b    >>=** f = Ex (t >>= f) (b >>=** f)
  p :===: q >>=** f = (p >>= f) :===: (q >>= f)

instance Syntax Problem where
  foldSyntax go bound free = \case
    Ex t b -> Ex (go free t) (foldSyntax go bound free b)
    p1 :===: p2 -> go free p1 :===: go free p2


exists :: (Eq a, Carrier sig m, Member Problem sig) => a ::: m a -> m a -> m a
exists (n ::: t) b = send (Ex t (bind1 n b))

unexists :: (Alternative m, Member Problem sig, HRModule sig) => a -> Term sig a -> m (a ::: Term sig a, Term sig a)
unexists n (Term t) | Just (Ex t b) <- prj t = pure (n ::: t, instantiate1 (pure n) b)
unexists _ _                                 = empty

(===) :: (Carrier sig m, Member Problem sig) => m a -> m a -> m a
p === q = send (p :===: q)

infixr 3 ===
