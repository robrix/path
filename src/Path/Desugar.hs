{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Desugar where

import Control.Effect hiding ((:+:))
import Control.Effect.Fresh
import Path.Core as Core
import Path.Name
import Path.Surface as Surface
import Path.Term
import Path.Usage

desugar :: (Applicative m, Carrier sig m, Member Fresh sig)
        => Term (Sugar Name :+: Implicit QName :+: Core Name QName) a
        -> m (Term (Implicit QName :+: Core Name QName) a)
desugar (In out span) = flip In span <$> case out of
  L (ForAll n t b) -> R <$> (Core.Pi n Zero <$> desugar t <*> desugar b)
  L ((u, a) :-> b) -> R <$> (Core.Pi <$> freshName <*> pure u <*> desugar a <*> desugar b)
  R rest -> traverse desugar rest

freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m Name
freshName = Gensym <$> fresh
