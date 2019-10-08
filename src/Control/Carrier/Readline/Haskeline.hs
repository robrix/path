{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, TypeOperators, UndecidableInstances #-}
module Control.Carrier.Readline.Haskeline
( -- * Readline effect
  module Control.Effect.Readline
  -- * Readline carrier
, runReadline
, ReadlineC(..)
  -- * MonadException
, runControlIO
, ControlIOC(..)
  -- * Re-exports
, Carrier
) where

import Control.Effect.Carrier
import Control.Effect.Lift
import Control.Effect.Reader
import Control.Effect.Readline
import Control.Monad.Fix
import Control.Monad.IO.Class
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

runControlIO :: (forall x . m x -> IO x) -> ControlIOC m a -> m a
runControlIO handler = runReader (Handler handler) . runControlIOC

newtype ControlIOC m a = ControlIOC { runControlIOC :: ReaderC (Handler m) m a }
  deriving (Applicative, Functor, Monad, MonadFix, MonadIO)

newtype Handler m = Handler (forall x . m x -> IO x)

runHandler :: Handler m -> ControlIOC m a -> IO a
runHandler h@(Handler handler) = handler . runReader h . runControlIOC

instance Carrier sig m => Carrier sig (ControlIOC m) where
  eff op = ControlIOC (eff (R (handleCoercible op)))

instance (Carrier sig m, MonadIO m) => MonadException (ControlIOC m) where
  controlIO f = ControlIOC $ do
    handler <- ask
    liftIO (f (RunIO (fmap pure . runHandler handler)) >>= runHandler handler)
