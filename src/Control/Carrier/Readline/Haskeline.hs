{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, TypeOperators, UndecidableInstances #-}
module Control.Carrier.Readline.Haskeline
( -- * Readline effect
  module Control.Effect.Readline
  -- * Readline carrier
, runReadline
, ReadlineC(..)
  -- * MonadException
, ControlIOC(..)
  -- * Re-exports
, Carrier
) where

import Control.Effect.Carrier
import Control.Effect.Lift
import Control.Effect.Reader
import Control.Effect.Readline
import Control.Monad.Fix
import Control.Monad.IO.Unlift
import Control.Monad.Trans
import Path.Pretty
import System.Console.Haskeline hiding (Handler, handle)

runReadline :: MonadException m => Prefs -> Settings m -> ReadlineC m a -> m a
runReadline prefs settings = runInputTWithPrefs prefs settings . runM . runReader (Line 0) . runReadlineC

newtype ReadlineC m a = ReadlineC { runReadlineC :: ReaderC Line (LiftC (InputT m)) a }
  deriving (Applicative, Functor, Monad, MonadFix, MonadIO)

instance (MonadException m, MonadIO m) => Carrier (Readline :+: Lift (InputT m)) (ReadlineC m) where
  eff (L (Prompt prompt k)) = ReadlineC $ do
    str <- lift (lift (getInputLine (cyan <> prompt <> plain)))
    local increment (runReadlineC (k str))
    where cyan = "\ESC[1;36m\STX"
          plain = "\ESC[0m\STX"
  eff (L (Print text k)) = putDoc text *> k
  eff (L (AskLine k)) = ReadlineC ask >>= k
  eff (R other) = ReadlineC (eff (R (handleCoercible other)))


newtype ControlIOC m a = ControlIOC { runControlIO :: m a }
  deriving (Applicative, Functor, Monad, MonadFix, MonadIO)

instance Carrier sig m => Carrier sig (ControlIOC m) where
  eff op = ControlIOC (eff (handleCoercible op))

instance MonadUnliftIO m => MonadUnliftIO (ControlIOC m) where
  withRunInIO inner = ControlIOC $ withRunInIO $ \go -> inner (go . runControlIO)

instance MonadUnliftIO m => MonadException (ControlIOC m) where
  controlIO f = withRunInIO (\ runInIO -> f (RunIO (fmap pure . runInIO)) >>= runInIO)
