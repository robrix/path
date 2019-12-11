{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, ScopedTypeVariables, TypeApplications, TypeOperators, UndecidableInstances #-}
module Control.Carrier.Readline.Haskeline
( -- * Readline carrier
  runReadline
, runReadlineWithHistory
, ReadlineC(..)
  -- * Readline effect
, module Control.Effect.Readline
) where

import Control.Algebra
import Control.Carrier.Lift
import Control.Carrier.Reader
import Control.Effect.Readline
import Control.Monad.Fix
import Control.Monad.IO.Class
import Data.Coerce
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal (renderIO)
import System.Console.Haskeline hiding (Handler, handle)
import System.Console.Terminal.Size as Size
import System.Directory
import System.FilePath
import System.IO (stdout)

runReadline :: MonadException m => Prefs -> Settings m -> ReadlineC m a -> m a
runReadline prefs settings = runInputTWithPrefs prefs (coerce settings) . runM . runReader (Line 0) . runReadlineC

runReadlineWithHistory :: MonadException m => ReadlineC m a -> m a
runReadlineWithHistory block = do
  homeDir <- liftIO getHomeDirectory
  prefs <- liftIO $ readPrefs (homeDir </> ".haskeline")
  let settingsDir = homeDir </> ".local" </> "semantic-core"
      settings = Settings
        { complete = noCompletion
        , historyFile = Just (settingsDir </> "repl_history")
        , autoAddHistory = True
        }
  liftIO $ createDirectoryIfMissing True settingsDir

  runReadline prefs settings block

newtype ReadlineC m a = ReadlineC { runReadlineC :: ReaderC Line (LiftC (InputT m)) a }
  deriving (Applicative, Functor, Monad, MonadFix, MonadIO)

instance MonadException m => Algebra Readline (ReadlineC m) where
  alg (Prompt prompt k) = ReadlineC $ do
    str <- sendM (getInputLine @m (cyan <> prompt <> plain))
    Line line <- ask
    local increment (runReadlineC (k line str))
    where cyan = "\ESC[1;36m\STX"
          plain = "\ESC[0m\STX"
  alg (Print doc k) = do
    s <- maybe 80 Size.width <$> liftIO size
    liftIO (renderIO stdout (layoutSmart defaultLayoutOptions { layoutPageWidth = AvailablePerLine s 0.8 } (doc <> line)))
    k


newtype Line = Line Int

increment :: Line -> Line
increment (Line n) = Line (n + 1)
