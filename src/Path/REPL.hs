{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, KindSignatures, LambdaCase, MultiParamTypeClasses, TypeOperators, UndecidableInstances #-}
module Path.REPL where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Sum
import Control.Monad ((<=<), unless)
import Control.Monad.IO.Class
import Data.Coerce
import Data.Foldable (for_)
import qualified Data.Map as Map
import Data.Text (Text, pack, unpack)
import Path.Context as Context
import Path.Elab
import Path.Env as Env
import Path.Eval
import Path.Module as Module
import Path.Name
import Path.Package
import Path.Parser (ErrInfo, Span, parseFile, parseString, whole)
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
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (</>), cyan, plain, putDoc)

data REPL (m :: * -> *) k
  = Prompt Text (Maybe Text -> k)
  | Output Text k
  deriving (Functor)

instance HFunctor REPL where
  hmap _ = coerce

instance Effect REPL where
  handle state handler = coerce . fmap (handler . (<$ state))

prompt :: (Carrier sig m, Member REPL sig) => Text -> m (Maybe Text)
prompt p = send (Prompt p ret)

output :: (Carrier sig m, Member REPL sig) => Text -> m ()
output s = send (Output s (ret ()))

runREPL :: (Carrier sig m, MonadIO m) => Prefs -> Settings IO -> Eff (REPLC m) a -> m a
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


repl :: MonadIO m => [FilePath] -> m ()
repl packageSources = do
  homeDir <- liftIO getHomeDirectory
  prefs <- liftIO (readPrefs (homeDir <> "/.haskeline"))
  let settingsDir = homeDir <> "/.local/path"
  liftIO $ createDirectoryIfMissing True settingsDir
  let settings = Settings
        { complete = noCompletion
        , historyFile = Just (settingsDir <> "/repl_history")
        , autoAddHistory = True
        }
  liftIO (runM
         (runREPL prefs settings
         (evalState (mempty :: ModuleTable QName)
         (evalState (Env.empty :: Env QName)
         (evalState (Context.empty :: Context QName)
         (evalState (Resolution mempty)
         (script packageSources)))))))

script :: ( Carrier sig m
          , Effect sig
          , Functor m
          , Member (Lift IO) sig
          , Member REPL sig
          , Member (State (Context QName)) sig
          , Member (State (Env QName)) sig
          , Member (State (ModuleTable QName)) sig
          , Member (State Resolution) sig
          )
       => [FilePath]
       -> m ()
script packageSources = evalState (ModuleGraph mempty :: ModuleGraph QName (Term (Surface QName) Span) Span) (runError (runError (runError (runError (runElab loop)))) >>= either printResolveError (either printElabError (either printModuleError (either printParserError pure))))
  where loop = do
          a <- prompt (pack "λ: ")
          maybe loop (runCommand <=< parseString (whole command) . unpack) a
            `catchError` (const loop <=< printResolveError)
            `catchError` (const loop <=< printElabError)
            `catchError` (const loop <=< printModuleError)
            `catchError` (const loop <=< printParserError)
        runCommand = \case
          Quit -> pure ()
          Help -> output helpText *> loop
          TypeOf tm -> do
            tm' <- runRenamer (resolveTerm tm)
            elab <- runInState Zero (infer tm')
            prettyPrint (ann elab)
            loop
          Decl decl -> do
            runRenamer (resolveDecl decl) >>= elabDecl
            loop
          Eval tm -> do
            tm' <- runRenamer (resolveTerm tm)
            elab <- runInState One (infer tm')
            get >>= prettyPrint . eval elab
            loop
          Show Bindings -> do
            ctx <- get
            unless (Context.null ctx) $ prettyPrint (ctx :: Context QName)
            env <- get
            unless (Env.null env) $ prettyPrint (env :: Env QName)
            loop
          Show Modules -> do
            graph <- get
            prettyPrint (vsep (map (pretty . moduleName) (modules (graph :: ModuleGraph QName (Term (Surface QName) Span) Span))))
            loop
          Reload -> reload *> loop
          Command.Import i -> do
            table <- get
            (ctx, env) <- raiseHandler (runReader (table :: ModuleTable QName)) (importModule i)
            modify (Context.union ctx)
            modify (Env.union env)
            loop
        reload = do
          put (Resolution mempty)
          let n = length packageSources
          sorted <- traverse (parseFile . whole . module' <*> id) packageSources >>= loadOrder . moduleGraph >>= traverse resolveModule

          for_ (zip [(1 :: Int)..] sorted) $ \ (i, m) -> do
            let name = moduleName m
            prettyPrint (brackets (pretty i <+> pretty "of" <+> pretty n) <+> pretty "Compiling" <+> pretty name <+> parens (pretty (modulePath m)))
            table <- get
            res <- raiseHandler (runReader (table :: ModuleTable QName)) (elabModule m)
            modify (Map.insert name res)
          put (moduleGraph sorted)
        runRenamer m = do
          res <- get
          raiseHandler (runReader (res :: Resolution) . runReader (ModuleName "(interpreter)")) m

printResolveError :: MonadIO m => ResolveError -> m ()
printResolveError = prettyPrint

printElabError :: MonadIO m => ElabError QName -> m ()
printElabError = prettyPrint

printModuleError :: MonadIO m => ModuleError -> m ()
printModuleError = prettyPrint

printParserError :: MonadIO m => ErrInfo -> m ()
printParserError = prettyPrint

basePackage :: Package
basePackage = Package
  { packageName        = "Base"
  , packageSources     =
      [ "src/Base/Applicative.path"
      , "src/Base/Bool.path"
      , "src/Base/Either.path"
      , "src/Base/Fin.path"
      , "src/Base/Fix.path"
      , "src/Base/Function.path"
      , "src/Base/Functor.path"
      , "src/Base/List.path"
      , "src/Base/Maybe.path"
      , "src/Base/Nat.path"
      , "src/Base/Pair.path"
      , "src/Base/Pointed.path"
      , "src/Base/Sigma.path"
      , "src/Base/Unit.path"
      , "src/Base/Vector.path"
      , "src/Base/Void.path"
      ]
  , packageConstraints = []
  }

helpText :: Text
helpText = pack
  $  ":help, :?   display this list of commands\n"
  <> ":quit, :q   exit the repl"
