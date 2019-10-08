{-# LANGUAGE DataKinds, DeriveGeneric, DeriveTraversable, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, StandaloneDeriving #-}
module Path.Scope where

import Data.Bifunctor
import Syntax.Fin as Fin
import Syntax.Nat
import Syntax.Scope
import Syntax.Var

strengthen :: Functor f => f (Var (Fin 'Z) a) -> f a
strengthen = fmap (unVar absurd id)


fromScopeFin :: Monad f => Scope () f (Var (Fin n) b) -> f (Var (Fin ('S n)) b)
fromScopeFin = instantiateVar (unVar (const (pure (B FZ))) (pure . first FS))

toScopeFin :: Applicative f => f (Var (Fin ('S n)) b) -> Scope () f (Var (Fin n) b)
toScopeFin = abstractVar (unVar (maybe (B ()) (F . B) . Fin.strengthen) (F . F))
