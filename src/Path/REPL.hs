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
import Data.Foldable (for_)
import qualified Data.Map as Map
import Data.Text (Text, pack, unpack)
import Data.Traversable (for)
import Path.Context as Context
import Path.Decl
import Path.Elab
import Path.Env as Env
import Path.Eval
import Path.Module as Module
import Path.Name
import Path.Package
import Path.Parser (Span, parseFile, parseString, whole)
import Path.Parser.Module (module')
import Path.Parser.REPL (command)
import Path.Pretty
import Path.Renamer
import Path.REPL.Command as Command
import Path.Surface
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
  liftIO (runM (runREPL prefs settings (evalState (mempty :: ModuleTable QName) (evalState (Env.empty :: Env QName) (evalState (Context.empty :: Context QName) (evalState (Resolution mempty) (script package)))))))

script :: (Carrier sig m, Effect sig, Functor m, Member (Lift IO) sig, Member REPL sig, Member (State (Context QName)) sig, Member (State (Env QName)) sig, Member (State (ModuleTable QName)) sig, Member (State Resolution) sig) => Package -> m ()
script package = evalState (ModuleGraph mempty :: ModuleGraph QName (Term (Surface QName) Span)) (runError (runError (runError (runElab (reload *> loop)))) >>= either prettyResolveError (either prettyElabError (either prettyModuleError pure)))
  where loop = do
          a <- prompt (pack "λ: ")
          maybe loop runCommand a
            `catchError` \ err -> prettyResolveError err >> loop
            `catchError` \ err -> prettyElabError err >> loop
            `catchError` \ err -> prettyModuleError err >> loop
        prettyResolveError err = prettyPrint (err :: ResolveError)
        prettyElabError err = prettyPrint (err :: ElabError QName)
        prettyModuleError err = prettyPrint (err :: ModuleError)
        runCommand s = case parseString (whole command) (unpack s) of
          Left err -> prettyPrint err *> loop
          Right Quit -> pure ()
          Right Help -> output helpText *> loop
          Right (TypeOf tm) -> do
            res <- get
            tm' <- raiseHandler (runReader (res :: Resolution) . runReader (ModuleName "(interpreter)")) (resolveTerm tm)
            elab <- runInState Zero (infer tm')
            prettyPrint (ann elab) >> loop
          Right (Decl decl) -> do
            res <- get
            decl' <- raiseHandler (runReader (res :: Resolution) . runReader (ModuleName "(interpreter)")) (resolveDecl decl)
            case decl' of
              Declare name ty -> elabDecl name ty
              Define  name tm -> elabDef  name tm
            loop
          Right (Eval tm) -> do
            res <- get
            tm' <- raiseHandler (runReader (res :: Resolution) . runReader (ModuleName "(interpreter)")) (resolveTerm tm)
            elab <- runInState One (infer tm')
            get >>= \ env -> prettyPrint (eval elab env) >> loop
          Right (Show Bindings) -> do
            ctx <- get
            prettyPrint (ctx :: Context QName)
            env <- get
            prettyPrint (env :: Env QName)
            loop
          Right Reload -> reload *> loop
          Right (Command.Import i) -> do
            table <- get
            res <- raiseHandler (runReader (table :: ModuleTable QName) . runError) (importModule (importModuleName i))
            case res of
              Left err -> prettyPrint (err :: ModuleError)
              Right (ctx, env) -> do
                modify (Context.union ctx)
                modify (Env.union env)
            loop
        reload = do
          let n = length (packageModules package)
          parsed <- for (packageModules package) $ \ name -> do
            res <- parseFile (whole module') (toPath name)
            case res of
              Left err -> Nothing <$ prettyPrint err
              Right a -> pure (Just a)
          let graph = maybe (ModuleGraph mempty) moduleGraph (sequenceA parsed)
          res <- runError (loadOrder graph)
          sorted <- case res of
            Left err -> [] <$ prettyPrint (err :: ModuleError)
            Right as -> resolveModules as

          for_ (zip [(1 :: Int)..] sorted) $ \ (i, m) -> do
            let name = moduleName m
            prettyPrint (brackets (pretty i <+> pretty "of" <+> pretty n) <+> pretty "Compiling" <+> pretty name <+> parens (pretty (toPath name)))
            table <- get
            res <- raiseHandler (runReader (table :: ModuleTable QName) . runError) (elabModule m)
            case res of
              Left err -> prettyPrint (err :: ModuleError)
              Right res -> modify (Map.insert name res)
          put (moduleGraph sorted)
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
      , ModuleName "Base" :. "Nat"
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
