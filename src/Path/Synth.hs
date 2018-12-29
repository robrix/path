{-# LANGUAGE FlexibleContexts #-}
module Path.Synth where

import Control.Effect
import Control.Effect.Reader
import Control.Effect.NonDet hiding (Branch(..))
import Control.Monad (unless)
import Data.Monoid (Alt(..))
import Path.Context as Context
import Path.Core as Core
import Path.Name
import Path.Resources as Resources
import Path.Term
import Path.Usage
import Path.Value

synth :: ( Carrier sig m
         , Effect sig
         , Member (Reader Context) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Type QName
      -> m (Maybe (Term (Core Name QName) (), Resources QName Usage, Type QName))
synth ty = runNonDetOnce (ask >>= tryInScopeVars ty . Context.filter (isLocal . getTerm))

tryInScopeVars :: (Alternative m, Carrier sig m, Member (Reader Usage) sig, Monad m) => Type QName -> Context -> m (Term (Core Name QName) (), Resources QName Usage, Type QName)
tryInScopeVars ty = getAlt . foldMap (Alt . tryVar) . unContext
  where tryVar (n ::: ty') = do
          unless (ty `aeq` ty') empty
          sigma <- ask
          pure (In (Core.Var n) (), Resources.singleton n sigma, ty')
