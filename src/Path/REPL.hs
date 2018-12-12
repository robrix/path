{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, KindSignatures, LambdaCase, MultiParamTypeClasses, TypeOperators, UndecidableInstances #-}
module Path.REPL where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Sum
import Control.Monad.IO.Class
import Data.Coerce
import Data.Foldable (for_, traverse_)
import qualified Data.Map as Map
import Path.Context as Context
import Path.Decl
import Path.Elab
import Path.Eval
import Path.Module
import Path.Parser (parseFile, parseString, whole)
import Path.Parser.Module (module')
import Path.Parser.REPL (command)
import Path.Pretty
import Path.REPL.Command
import Path.Term
import Path.Usage
import System.Console.Haskeline
import System.Directory (createDirectoryIfMissing, getHomeDirectory)
import Text.PrettyPrint.ANSI.Leijen hiding (cyan, plain, putDoc)

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
  liftIO (runM (runREPL prefs settings (evalState (mempty :: ModuleTable) (evalState (mempty :: Env) (evalState (Context.empty :: Context) script)))))

script :: (Carrier sig m, Effect sig, Member REPL sig, Member (State Context) sig, Member (State Env) sig, Member (State ModuleTable) sig, MonadIO m) => m ()
script = do
  a <- prompt "λ: "
  maybe script runCommand a
  where runCommand s = case parseString (whole command) s of
          Left err -> prettyPrint err *> script
          Right Quit -> pure ()
          Right Help -> output helpText *> script
          Right (TypeOf tm) -> do
            res <- runElabError (runInState Zero (infer tm))
            case res of
              Left err -> prettyPrint err >> script
              Right elab -> prettyPrint (ann elab) >> script
          Right (Decl decl) -> do
            res <- runElabError (case decl of
              Declare name ty -> elabDecl name ty
              Define  name tm -> elabDef  name tm)
            case res of
              Left err -> prettyPrint err *> script
              Right _ -> script
          Right (Eval tm) -> do
            res <- runElabError (runInState One (infer tm))
            case res of
              Left err -> prettyPrint err >> script
              Right elab -> get >>= \ env -> prettyPrint (eval elab env) >> script
          Right (Show Bindings) -> do
            ctx <- get
            prettyPrint (ctx :: Context)
            env <- get
            traverse_ (putDoc . prettyEnv) (Map.toList (env :: Env))
            script
          Right (Load moduleName) -> load moduleName *> script
        load name = do
          res <- parseFile (whole module') (toPath name)
          case res of
            Left err -> prettyPrint err
            Right m -> do
              for_ (moduleImports m) $ \ (Import name') ->
                load name'
              table <- get
              res <- runReader (table :: ModuleTable) (runError (runElabError (elabModule m)))
              case res of
                Left err -> prettyPrint (err :: ModuleError)
                Right (Left err) -> prettyPrint err
                Right (Right res) -> modify (Map.insert name res)
        prettyEnv (name, tm) = pretty name <+> pretty "=" <+> group (pretty tm)
        toPath s = "src/" <> go s <> ".path"
          where go (ModuleName s) = s
                go (ss :. s)      = go ss <> "/" <> s


helpText :: String
helpText
  =  ":help, :?   display this list of commands\n"
  <> ":quit, :q   exit the repl"
