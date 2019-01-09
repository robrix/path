{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Desugar where

import Control.Effect hiding ((:+:))
import Control.Effect.Fresh
import Path.Core as Core
import Path.Implicit
import Path.Name
import Path.Plicity
import Path.Surface as Surface
import Path.Term

desugar :: (Applicative m, Carrier sig m, Member Fresh sig)
        => Term (Sugar Name :+: Implicit QName :+: Core Name QName) a
        -> m (Term (Implicit QName :+: Core Name QName) a)
desugar (In out span) = flip In span <$> case out of
  L ((u, a) :-> b) -> R <$> (Core.Pi <$> freshName <*> pure Ex <*> pure u <*> desugar a <*> desugar b)
  R rest -> traverse desugar rest

freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m Name
freshName = Gensym "_" <$> fresh
