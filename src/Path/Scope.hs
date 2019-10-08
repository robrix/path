{-# LANGUAGE DataKinds, DeriveGeneric, DeriveTraversable, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, StandaloneDeriving #-}
module Path.Scope where

import Control.Monad ((>=>))
import Data.Bifunctor
import Path.Fin
import Path.Nat
import Syntax.Scope
import Syntax.Var

match :: Applicative f => (b -> Var a c) -> b -> Var a (f c)
match f x = unVar B (F . pure) (f x)


strengthen :: Functor f => f (Var (Fin 'Z) a) -> f a
strengthen = fmap (unVar absurdFin id)


fromScopeFin :: Monad f => Scope () f (Var (Fin n) b) -> f (Var (Fin ('S n)) b)
fromScopeFin = unScope >=> unVar (const (pure (B FZ))) (fmap (first FS))

toScopeFin :: Applicative f => f (Var (Fin ('S n)) b) -> Scope () f (Var (Fin n) b)
toScopeFin = Scope . fmap (match (unVar (maybe (B ()) (F . B) . strengthenFin) (F . F)))
