{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, KindSignatures, LambdaCase, MultiParamTypeClasses, TypeOperators, UndecidableInstances #-}
module Path.REPL where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Fail
import Control.Effect.Reader
import Control.Effect.Sum
import Control.Monad.IO.Class
import Data.Coerce
import Path.Elab
import Path.Eval
import Path.Parser (Command(..), command, parseString, whole)
import System.Console.Haskeline
import System.Directory (createDirectoryIfMissing, getHomeDirectory)

data REPL (m :: * -> *) k
  = Prompt String (Maybe String -> k)
  | Output String k
  deriving (Functor)

instance HFunctor REPL where
  hmap _ = coerce

instance Effect REPL where
  handle state handler = coerce . fmap (handler . (<$ state))

prompt :: (Member REPL sig, Carrier sig m) => String -> m (Maybe String)
prompt p = send (Prompt p ret)

output :: (Member REPL sig, Carrier sig m) => String -> m ()
output s = send (Output s (ret ()))

runREPL :: (MonadIO m, Carrier sig m) => Prefs -> Settings IO -> Eff (REPLC m) a -> m a
runREPL prefs settings = flip runREPLC (prefs, settings) . interpret

newtype REPLC m a = REPLC { runREPLC :: (Prefs, Settings IO) -> m a }

instance (Carrier sig m, MonadIO m) => Carrier (REPL :+: sig) (REPLC m) where
  ret = REPLC . const . ret
  eff op = REPLC (\ args -> handleSum (eff . handleReader args runREPLC) (\case
    Prompt p k -> liftIO (uncurry runInputTWithPrefs args (getInputLine (cyan <> p <> plain))) >>= flip runREPLC args . k
    Output s k -> liftIO (uncurry runInputTWithPrefs args (outputStrLn s)) *> runREPLC k args) op)

cyan :: String
cyan = "\ESC[1;36m\STX"

plain :: String
plain = "\ESC[0m\STX"


repl :: MonadIO m => m ()
repl = do
  homeDir <- liftIO getHomeDirectory
  prefs <- liftIO (readPrefs (homeDir <> "/.haskeline"))
  let settingsDir = homeDir <> "/.local/path"
  liftIO $ createDirectoryIfMissing True settingsDir
  let settings = Settings
        { complete = noCompletion
        , historyFile = Just (settingsDir <> "/repl_history")
        , autoAddHistory = True
        }
  liftIO (runM (runREPL prefs settings script))

script :: (Carrier sig m, Member REPL sig, Monad m) => m ()
script = do
  a <- prompt "λ: "
  maybe script runCommand a
  where runCommand s = case parseString (whole command) s of
          Left err -> output err *> script
          Right Quit -> pure ()
          Right Help -> output helpText *> script
          Right (Type tm) -> case run (runFail (runReader (mempty :: Context) (infer tm))) of
            Left err -> output err *> script
            Right elab -> output (show (elabType elab)) *> script
          Right (Eval tm) -> case run (runFail (runReader (mempty :: Context) (infer tm))) of
            Left err -> output err *> script
            Right elab -> output (show (eval (erase elab) mempty)) *> script

helpText :: String
helpText
  =  ":help, :?   display this list of commands\n"
  <> ":quit, :q   exit the repl"
