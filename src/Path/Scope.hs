{-# LANGUAGE DataKinds, DeriveGeneric, DeriveTraversable, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, StandaloneDeriving #-}
module Path.Scope where

import Control.Monad ((>=>))
import Data.Bifunctor
import Syntax.Fin as Fin
import Syntax.Nat
import Syntax.Scope
import Syntax.Var

strengthen :: Functor f => f (Var (Fin 'Z) a) -> f a
strengthen = fmap (unVar absurd id)


fromScopeFin :: Monad f => Scope () f (Var (Fin n) b) -> f (Var (Fin ('S n)) b)
fromScopeFin = unScope >=> unVar (const (pure (B FZ))) (fmap (first FS))

toScopeFin :: Applicative f => f (Var (Fin ('S n)) b) -> Scope () f (Var (Fin n) b)
toScopeFin = Scope . fmap (unVar (maybe (B ()) (F . pure . B) . Fin.strengthen) (F . pure . F))
