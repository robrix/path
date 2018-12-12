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
import Data.Text (Text, pack, unpack)
import Path.Context as Context
import Path.Decl
import Path.Elab
import Path.Eval
import Path.Module
import Path.Package
import Path.Parser (parseFile, parseString, whole)
import Path.Parser.Module (module')
import Path.Parser.REPL (command)
import Path.Pretty
import Path.REPL.Command
import Path.Term
import Path.Usage
import System.Console.Haskeline
import System.Directory (createDirectoryIfMissing, getHomeDirectory)
import System.FilePath.Posix
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (</>), cyan, plain, putDoc)

data REPL (m :: * -> *) k
  = Prompt Text (Maybe Text -> k)
  | Output Text k
  deriving (Functor)

instance HFunctor REPL where
  hmap _ = coerce

instance Effect REPL where
  handle state handler = coerce . fmap (handler . (<$ state))

prompt :: (Member REPL sig, Carrier sig m) => Text -> m (Maybe Text)
prompt p = send (Prompt p ret)

output :: (Member REPL sig, Carrier sig m) => Text -> m ()
output s = send (Output s (ret ()))

runREPL :: (MonadIO m, Carrier sig m) => Prefs -> Settings IO -> Eff (REPLC m) a -> m a
runREPL prefs settings = flip runREPLC (prefs, settings) . interpret

newtype REPLC m a = REPLC { runREPLC :: (Prefs, Settings IO) -> m a }

instance (Carrier sig m, MonadIO m) => Carrier (REPL :+: sig) (REPLC m) where
  ret = REPLC . const . ret
  eff op = REPLC (\ args -> handleSum (eff . handleReader args runREPLC) (\case
    Prompt p k -> liftIO (uncurry runInputTWithPrefs args (fmap pack <$> getInputLine (cyan <> unpack p <> plain))) >>= flip runREPLC args . k
    Output s k -> liftIO (uncurry runInputTWithPrefs args (outputStrLn (unpack s))) *> runREPLC k args) op)

cyan :: String
cyan = "\ESC[1;36m\STX"

plain :: String
plain = "\ESC[0m\STX"


repl :: MonadIO m => Package -> m ()
repl package = do
  homeDir <- liftIO getHomeDirectory
  prefs <- liftIO (readPrefs (homeDir <> "/.haskeline"))
  let settingsDir = homeDir <> "/.local/path"
  liftIO $ createDirectoryIfMissing True settingsDir
  let settings = Settings
        { complete = noCompletion
        , historyFile = Just (settingsDir <> "/repl_history")
        , autoAddHistory = True
        }
  liftIO (runM (runREPL prefs settings (evalState (mempty :: ModuleTable) (evalState (mempty :: Env) (evalState (Context.empty :: Context) (script package))))))

script :: (Carrier sig m, Effect sig, Member REPL sig, Member (State Context) sig, Member (State Env) sig, Member (State ModuleTable) sig, MonadIO m) => Package -> m ()
script package = loop
  where loop = do
          a <- prompt (pack "λ: ")
          maybe loop runCommand a
        runCommand s = case parseString (whole command) (unpack s) of
          Left err -> prettyPrint err *> loop
          Right Quit -> pure ()
          Right Help -> output helpText *> loop
          Right (TypeOf tm) -> do
            res <- runElabError (runInState Zero (infer tm))
            case res of
              Left err -> prettyPrint err >> loop
              Right elab -> prettyPrint (ann elab) >> loop
          Right (Decl decl) -> do
            res <- runElabError (case decl of
              Declare name ty -> elabDecl name ty
              Define  name tm -> elabDef  name tm)
            case res of
              Left err -> prettyPrint err *> loop
              Right _ -> loop
          Right (Eval tm) -> do
            res <- runElabError (runInState One (infer tm))
            case res of
              Left err -> prettyPrint err >> loop
              Right elab -> get >>= \ env -> prettyPrint (eval elab env) >> loop
          Right (Show Bindings) -> do
            ctx <- get
            prettyPrint (ctx :: Context)
            env <- get
            traverse_ (putDoc . prettyEnv) (Map.toList (env :: Env))
            loop
          Right (Load moduleName) -> load moduleName *> loop
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
        toPath s = packageSourceDir package </> go s <> ".path"
          where go (ModuleName s) = s
                go (ss :. s)      = go ss <> "/" <> s

basePackage :: Package
basePackage = Package
  { packageName        = "Base"
  , packageSourceDir   = "src"
  , packageModules     =
      [ ModuleName "Base" :. "Bool"
      , ModuleName "Base" :. "Either"
      , ModuleName "Base" :. "Fix"
      , ModuleName "Base" :. "Function"
      , ModuleName "Base" :. "Maybe"
      , ModuleName "Base" :. "Pair"
      , ModuleName "Base" :. "Unit"
      , ModuleName "Base" :. "Void"
      ]
  , packageConstraints = []
  }

helpText :: Text
helpText = pack
  $  ":help, :?   display this list of commands\n"
  <> ":quit, :q   exit the repl"
