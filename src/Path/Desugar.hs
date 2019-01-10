{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Desugar where

import Control.Effect hiding ((:+:))
import Control.Effect.Fresh
import Path.Core as Core
import Path.Name
import Path.Plicity
import qualified Path.Surface as Surface
import Path.Term

desugar :: (Applicative m, Carrier sig m, Member Fresh sig)
        => Term (Surface.Surface Name QName) a
        -> m (Term (Core Name QName) a)
desugar (In out span) = flip In span <$> case out of
  Surface.Free v -> pure (Core.Free v)
  Surface.Lam n b -> Core.Lam n <$> desugar b
  f Surface.:$ a -> (Core.:$) <$> desugar f <*> desugar a
  Surface.Type -> pure Core.Type
  Surface.Pi n p u t b -> Core.Pi n p u <$> desugar t <*> desugar b
  Surface.Hole v -> pure (Core.Hole v)
  (u, a) Surface.:-> b -> Core.Pi <$> freshName <*> pure Ex <*> pure u <*> desugar a <*> desugar b

freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m Name
freshName = Gensym "_" <$> fresh
