{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.REPL where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Sum
import Control.Monad ((<=<), join, unless)
import Control.Monad.IO.Class
import Control.Monad.Trans (MonadTrans(..))
import Data.Coerce
import Data.Foldable (for_)
import Data.Int (Int64)
import qualified Data.Map as Map
import qualified Data.Text as T
import Path.Context as Context
import Path.Elab
import Path.Env as Env
import Path.Eval
import Path.Module as Module
import Path.Name
import Path.Package
import Path.Parser (Delta(..), ErrInfo, Parser, Span, parseFile, parseString, whole)
import Path.Parser.Module (module')
import Path.Parser.REPL (command)
import Path.Pretty
import Path.Renamer
import Path.REPL.Command as Command
import Path.Surface
import Path.Term
import Path.Usage
import System.Console.Haskeline hiding (handle)
import System.Directory (createDirectoryIfMissing, getHomeDirectory)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (</>), putDoc)

data REPL cmd (m :: * -> *) k
  = Prompt T.Text (Maybe cmd -> k)
  | Output T.Text k
  deriving (Functor)

instance HFunctor (REPL cmd) where
  hmap _ = coerce

instance Effect (REPL cmd) where
  handle state handler = coerce . fmap (handler . (<$ state))

prompt :: (Carrier sig m, Member (REPL cmd) sig) => T.Text -> m (Maybe cmd)
prompt p = send (Prompt p ret)

output :: (Carrier sig m, Member (REPL Command) sig) => T.Text -> m ()
output s = sendREPL (Output s (ret ()))

sendREPL :: (Carrier sig m, Member (REPL Command) sig) => REPL Command m (m a) -> m a
sendREPL = send

runREPL :: (Carrier sig m, Effect sig, Member (Lift IO) sig, MonadException m) => Parser (Maybe cmd) -> Prefs -> Settings m -> Eff (REPLC cmd m) a -> m a
runREPL parser prefs settings = runInputTWithPrefs prefs settings . runREPLC parser (Line 0) . interpret

newtype REPLC cmd m a = REPLC (Parser (Maybe cmd) -> Line -> InputT m a)

runREPLC :: Parser (Maybe cmd) -> Line -> REPLC cmd m a -> InputT m a
runREPLC p l (REPLC m) = m p l

instance (Carrier sig m, Effect sig, Member (Lift IO) sig, MonadException m) => Carrier (REPL cmd :+: sig) (REPLC cmd m) where
  ret = REPLC . const . const . pure
  eff op = REPLC (\ c l -> handleSum (join . lift . eff . handle (pure ()) (pure . (runREPLC c l =<<))) (\case
    Prompt prompt k -> do
      str <- getInputLine (cyan <> T.unpack prompt <> plain)
      res <- lift (runError (traverse (parseString c (lineDelta l)) str))
      res <- case res of
        Left  err -> printParserError err >> pure Nothing
        Right res -> pure (join res)
      runREPLC c (increment l) (k res)
    Output text k -> outputStrLn (T.unpack text) *> runREPLC c l k) op)
    where cyan = "\ESC[1;36m\STX"
          plain = "\ESC[0m\STX"

newtype ControlIOC m a = ControlIOC ((forall x . m x -> IO x) -> m a)

instance Functor m => Functor (ControlIOC m) where
  fmap f (ControlIOC g) = ControlIOC (\ h -> fmap f (g h))

instance Applicative m => Applicative (ControlIOC m) where
  pure a = ControlIOC (const (pure a))
  ControlIOC f <*> ControlIOC a = ControlIOC (\ h -> f h <*> a h)

instance Monad m => Monad (ControlIOC m) where
  return = pure
  ControlIOC m >>= f = ControlIOC (\ handler -> m handler >>= runControlIOC handler . f)

instance MonadIO m => MonadIO (ControlIOC m) where
  liftIO m = ControlIOC (const (liftIO m))

runControlIOC :: (forall x . m x -> IO x) -> ControlIOC m a -> m a
runControlIOC f (ControlIOC m) = m f

instance Carrier sig m => Carrier sig (ControlIOC m) where
  ret a = ControlIOC (const (ret a))
  eff op = ControlIOC (\ handler -> eff (handlePure (runControlIOC handler) op))

instance MonadIO m => MonadException (ControlIOC m) where
  controlIO f = ControlIOC (\ handler -> liftIO (f (RunIO (fmap pure . handler . runControlIOC handler)) >>= handler . runControlIOC handler))

repl :: MonadIO m => [FilePath] -> m ()
repl packageSources = liftIO $ do
  homeDir <- getHomeDirectory
  prefs <- readPrefs (homeDir <> "/.haskeline")
  let settingsDir = homeDir <> "/.local/path"
      settings = Settings
        { complete = noCompletion
        , historyFile = Just (settingsDir <> "/repl_history")
        , autoAddHistory = True
        }
  createDirectoryIfMissing True settingsDir
  runM (runControlIOC runM
       (runREPL command prefs settings
       (evalState (mempty :: ModuleTable QName)
       (evalState (Env.empty :: Env QName)
       (evalState (Context.empty :: Context QName)
       (evalState (Resolution mempty)
       (script packageSources)))))))

newtype Line = Line Int64

increment :: Line -> Line
increment (Line n) = Line (n + 1)

lineDelta :: Line -> Delta
lineDelta (Line l) = Lines l 0 0 0

script :: ( Carrier sig m
          , Effect sig
          , Functor m
          , Member (Lift IO) sig
          , Member (REPL Command) sig
          , Member (State (Context QName)) sig
          , Member (State (Env QName)) sig
          , Member (State (ModuleTable QName)) sig
          , Member (State Resolution) sig
          )
       => [FilePath]
       -> m ()
script packageSources = evalState (ModuleGraph mempty :: ModuleGraph QName (Term (Surface QName) Span) Span) (runError (runError (runError (runError (runElab loop)))) >>= either printResolveError (either printElabError (either printModuleError (either printParserError pure))))
  where loop = (prompt (T.pack "λ: ") >>= maybe loop runCommand)
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
      , "src/Base/Monad.path"
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

helpText :: T.Text
helpText = T.pack
  $  ":help, :?   display this list of commands\n"
  <> ":quit, :q   exit the repl"
