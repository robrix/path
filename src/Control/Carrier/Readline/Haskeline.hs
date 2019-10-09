{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators, UndecidableInstances #-}
module Control.Carrier.Readline.Haskeline
( -- * Readline effect
  module Control.Effect.Readline
  -- * Readline carrier
, runReadline
, ReadlineC(..)
  -- * Re-exports
, Carrier
) where

import Control.Carrier
import Control.Carrier.Lift
import Control.Carrier.Reader
import Control.Effect.Readline
import Control.Monad.Fix
import Control.Monad.IO.Unlift
import Data.Coerce
import Path.Pretty
import System.Console.Haskeline hiding (Handler, handle)

runReadline :: MonadUnliftIO m => Prefs -> Settings m -> ReadlineC m a -> m a
runReadline prefs settings = runControlIO . runInputTWithPrefs prefs (coerce settings) . runM . runReader (Line 0) . runReadlineC

newtype ReadlineC m a = ReadlineC { runReadlineC :: ReaderC Line (LiftC (InputT (ControlIO m))) a }
  deriving (Applicative, Functor, Monad, MonadFix, MonadIO)

instance MonadUnliftIO m => Carrier (Readline :+: Lift (InputT (ControlIO m))) (ReadlineC m) where
  eff (L (Prompt prompt k)) = ReadlineC $ do
    str <- sendM (getInputLine @(ControlIO m) (cyan <> prompt <> plain))
    line <- ask
    local increment (runReadlineC (k line str))
    where cyan = "\ESC[1;36m\STX"
          plain = "\ESC[0m\STX"
  eff (L (Print text k)) = putDoc text *> k
  eff (R other) = ReadlineC (eff (R (handleCoercible other)))


newtype ControlIO m a = ControlIO { runControlIO :: m a }
  deriving (Applicative, Functor, Monad, MonadFix, MonadIO)

instance MonadUnliftIO m => MonadUnliftIO (ControlIO m) where
  withRunInIO inner = ControlIO $ withRunInIO $ \go -> inner (go . runControlIO)

instance MonadUnliftIO m => MonadException (ControlIO m) where
  controlIO f = withRunInIO (\ runInIO -> f (RunIO (fmap pure . runInIO)) >>= runInIO)
