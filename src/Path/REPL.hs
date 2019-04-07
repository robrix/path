{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.REPL where

import Control.Arrow ((&&&))
import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Sum as Effect
import Control.Monad ((<=<), join, unless)
import Control.Monad.IO.Class
import Control.Monad.Trans (MonadTrans(..))
import Data.Bool (bool)
import Data.Coerce
import Data.Foldable (for_)
import Data.Int (Int64)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Path.Elab
import Path.Eval
import Path.Module as Module
import Path.Name
import Path.Package
import Path.Parser (Delta(..), parseString, whole)
import Path.Parser.Module (parseModule)
import Path.Parser.REPL (command)
import Path.Pretty
import Path.Renamer
import Path.REPL.Command as Command
import qualified Path.Scope as Scope
import Path.Stack
import Path.Value
import Prelude hiding (print)
import System.Console.Haskeline hiding (Handler, handle)
import System.Directory (createDirectoryIfMissing, getHomeDirectory)
import Text.Trifecta.Rendering (Span(..), Spanned(..))

data REPL (m :: * -> *) k
  = Prompt String (Maybe String -> k)
  | Print Doc k
  | AskLine (Line -> k)
  deriving (Functor)

instance HFunctor REPL where
  hmap _ = coerce

instance Effect REPL where
  handle state handler = coerce . fmap (handler . (<$ state))


prompt :: (Carrier sig m, Member REPL sig) => String -> m (Maybe String)
prompt p = send (Prompt p pure)

print :: (Pretty a, Carrier sig m, Member REPL sig) => a -> m ()
print s = send (Print (pretty s) (pure ()))

askLine :: (Carrier sig m, Member REPL sig) => m Line
askLine = send (AskLine pure)


runREPL :: MonadException m => Prefs -> Settings m -> REPLC m a -> m a
runREPL prefs settings = runInputTWithPrefs prefs settings . runTransC . runReader (Line 0) . runREPLC

newtype REPLC m a = REPLC { runREPLC :: ReaderC Line (TransC InputT m) a }
  deriving (Applicative, Functor, Monad, MonadIO)

instance (Carrier sig m, Effect sig, MonadException m, MonadIO m) => Carrier (REPL :+: sig) (REPLC m) where
  eff (L (Prompt prompt k)) = REPLC $ do
    str <- lift (TransC (getInputLine (cyan <> prompt <> plain)))
    local increment (runREPLC (k str))
    where cyan = "\ESC[1;36m\STX"
          plain = "\ESC[0m\STX"
  eff (L (Print text k)) = putDoc text *> k
  eff (L (AskLine k)) = REPLC ask >>= k
  eff (R other) = REPLC (eff (R (handleCoercible other)))

newtype TransC t (m :: * -> *) a = TransC { runTransC :: t m a }
  deriving (Applicative, Functor, Monad, MonadIO, MonadTrans)

instance (Carrier sig m, Effect sig, Monad (t m), MonadTrans t) => Carrier sig (TransC t m) where
  eff = TransC . join . lift . eff . handle (pure ()) (pure . (runTransC =<<))

runControlIO :: (forall x . m x -> IO x) -> ControlIOC m a -> m a
runControlIO handler = runReader (Handler handler) . runControlIOC

newtype ControlIOC m a = ControlIOC { runControlIOC :: ReaderC (Handler m) m a }
  deriving (Applicative, Functor, Monad, MonadIO)

newtype Handler m = Handler (forall x . m x -> IO x)

runHandler :: Handler m -> ControlIOC m a -> IO a
runHandler h@(Handler handler) = handler . runReader h . runControlIOC

instance Carrier sig m => Carrier sig (ControlIOC m) where
  eff op = ControlIOC (eff (R (handleCoercible op)))

instance (Carrier sig m, MonadIO m) => MonadException (ControlIOC m) where
  controlIO f = ControlIOC $ do
    handler <- ask
    liftIO (f (RunIO (fmap pure . runHandler handler)) >>= runHandler handler)

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
  runM (runControlIO runM
       (runREPL prefs settings
       (evalState (mempty :: ModuleTable)
       (evalState (mempty :: Scope.Scope)
       (evalState (Resolution mempty)
       (runNaming (Root "repl")
       (script packageSources)))))))

newtype Line = Line Int64

increment :: Line -> Line
increment (Line n) = Line (n + 1)

lineDelta :: Line -> Delta
lineDelta (Line l) = Lines l 0 0 0

script :: ( Carrier sig m
          , Effect sig
          , Member Naming sig
          , Member REPL sig
          , Member (State ModuleTable) sig
          , Member (State Resolution) sig
          , Member (State Scope.Scope) sig
          , MonadIO m
          )
       => [FilePath]
       -> m ()
script packageSources = evalState (ModuleGraph mempty :: ModuleGraph Qualified (Value Name ::: Type Name)) (runError loop >>= either (print @Doc) pure)
  where loop = (prompt "λ: " >>= parseCommand >>= maybe loop runCommand . join)
          `catchError` (const loop <=< print @Doc)
        parseCommand str = do
          l <- askLine
          traverse (parseString (whole command) (lineDelta l)) str
        runCommand = \case
          Quit -> pure ()
          Help -> print helpDoc *> loop
          TypeOf tm -> elaborate tm >>= print . typedType >> loop
          Command.Decl decl -> do
            _ <- runRenamer (resolveDecl decl) >>= elabDecl
            loop
          Eval tm -> elaborate tm >>= gets . flip whnf . typedTerm >>= print >> loop
          Show Bindings -> do
            scope <- get
            unless (Scope.null scope) $ print scope
            loop
          Show Modules -> do
            graph <- get
            let ms = modules (graph :: ModuleGraph Qualified (Value Name ::: Type Name))
            unless (Prelude.null ms) $ print (tabulate2 space (map (moduleName &&& parens . pretty . modulePath) ms))
            loop
          Reload -> reload *> loop
          Command.Import i -> do
            table <- get
            runReader (table :: ModuleTable) (importModule i) >>= modify . Scope.union
            loop
          Command.Doc moduleName -> do
            m <- gets (Map.lookup moduleName . unModuleGraph)
            case m :: Maybe (Module Qualified (Value Name ::: Type Name)) of
              Just m -> case moduleDocs m of
                Just d  -> print (pretty d)
                Nothing -> print (pretty "no docs for" <+> squotes (pretty moduleName))
              Nothing   -> print (pretty "no such module" <+> squotes (pretty moduleName))
            loop
        reload = do
          put (Resolution mempty)
          let n = length packageSources
          sorted <- traverse parseModule packageSources >>= loadOrder . moduleGraph

          checked <- runDeps . for (zip [(1 :: Int)..] sorted) $ \ (i, m) -> skipDeps m $ do
            let name    = moduleName m
                ordinal = brackets (pretty i <+> pretty "of" <+> pretty n)
                path    = parens (pretty (modulePath m))
            print (ordinal <+> pretty "Compiling" <+> pretty name <+> path)
            table <- get
            (errs, (scope, res)) <- runState Nil (runReader (table :: ModuleTable) (runState (mempty :: Scope.Scope) (runReader (Span mempty mempty mempty) (resolveModule m) >>= elabModule)))
            if Prelude.null errs then
              modify (Map.insert name scope)
            else do
              for_ errs (print @Doc)
              modify (name:)
            pure (Just res)
          put (moduleGraph (catMaybes checked))
        runDeps = evalState ([] :: [ModuleName])
        skipDeps m a = gets (failedDep m) >>= bool (Nothing <$ modify (moduleName m:)) a
        failedDep m = all @[] (`notElem` map (importModuleName . unSpanned) (moduleImports m))
        unSpanned (a :~ _) = a
        runRenamer m = do
          res <- get
          runReader (res :: Resolution) (runReader (ModuleName "(interpreter)") m)
        elaborate (tm :~ span) = runReader span $ do
          ty <- inferType
          tm' <- runRenamer (runReader Defn (resolveTerm tm))
          runScope (define ty (elab tm'))

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
      , "src/Base/Lazy.path"
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

helpDoc :: Doc
helpDoc = tabulate2 (space <+> space) entries
  where entries =
          [ (":help, :?",        w "display this list of commands")
          , (":quit, :q",        w "exit the repl")
          , (":reload, :r",      w "reload the current package")
          , (":type, :t <expr>", w "show the type of <expr>")
          ]
        w = align . fillSep . map pretty . words
