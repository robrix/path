{-# LANGUAGE DeriveAnyClass, DeriveFunctor, DeriveGeneric, DerivingStrategies, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, RankNTypes, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.REPL where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Sum as Effect
import Control.Monad ((<=<), foldM, join, unless)
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Trans (MonadTrans(..))
import Data.Foldable (for_)
import Data.Int (Int64)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void
import GHC.Generics (Generic1)
import Path.Core
import Path.Elab
import Path.Eval
import Path.Module as Module
import Path.Name
import qualified Path.Namespace as Namespace
import Path.Package
import Path.Parser (Delta(..), parseString, whole)
import Path.Parser.Module (parseModule)
import Path.Parser.REPL (command)
import Path.Pretty
import Path.REPL.Command as Command
import Path.Scope
import Path.Span
import Path.Stack
import qualified Path.Surface as Surface
import Prelude hiding (print)
import System.Console.Haskeline hiding (Handler, handle)
import System.Directory (createDirectoryIfMissing, getHomeDirectory)

data REPL m k
  = Prompt String (Maybe String -> m k)
  | Print Doc (m k)
  | AskLine (Line -> m k)
  deriving stock (Functor, Generic1)
  deriving anyclass (Effect, HFunctor)


prompt :: (Carrier sig m, Member REPL sig) => String -> m (Maybe String)
prompt p = send (Prompt p pure)

print :: (Pretty a, Carrier sig m, Member REPL sig) => a -> m ()
print s = send (Print (pretty s) (pure ()))

askLine :: (Carrier sig m, Member REPL sig) => m Line
askLine = send (AskLine pure)


runREPL :: MonadException m => Prefs -> Settings m -> REPLC m a -> m a
runREPL prefs settings = runInputTWithPrefs prefs settings . runTransC . runReader (Line 0) . runREPLC

newtype REPLC m a = REPLC { runREPLC :: ReaderC Line (TransC InputT m) a }
  deriving newtype (Applicative, Functor, Monad, MonadFix, MonadIO)

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
  deriving newtype (Applicative, Functor, Monad, MonadFix, MonadIO, MonadTrans)

instance (Carrier sig m, Effect sig, Monad (t m), MonadTrans t) => Carrier sig (TransC t m) where
  eff = TransC . join . lift . eff . handle (pure ()) (pure . (runTransC =<<))

runControlIO :: (forall x . m x -> IO x) -> ControlIOC m a -> m a
runControlIO handler = runReader (Handler handler) . runControlIOC

newtype ControlIOC m a = ControlIOC { runControlIOC :: ReaderC (Handler m) m a }
  deriving newtype (Applicative, Functor, Monad, MonadFix, MonadIO)

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
       (evalState (mempty :: Namespace.Namespace)
       (runReader (ModuleName "(interpreter)")
       (runNaming
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
          , Member (Reader ModuleName) sig
          , Member (State ModuleTable) sig
          , Member (State Namespace.Namespace) sig
          , MonadIO m
          )
       => [FilePath]
       -> m ()
script packageSources
  = evalState (ModuleGraph mempty :: ModuleGraph Core Void)
  . evalState (mempty @(Set.Set ModuleName))
  $ runError loop >>= either (print @Doc) pure
  where loop = (prompt "λ: " >>= parseCommand >>= maybe loop runCommand . join)
          `catchError` (const loop <=< print @Doc)
        parseCommand str = do
          l <- askLine
          traverse (parseString (whole command) (lineDelta l)) str
        runCommand = \case
          Quit -> pure ()
          Help -> print helpDoc *> loop
          TypeOf tm -> elaborate tm >>= print . typedType . unSpanned >> loop
          Command.Decl decl -> runSubgraph (asks @(ModuleGraph Core Void) (fmap unScopeH . unModuleGraph) >>= flip renameDecl decl >>= elabDecl) >> loop
          Eval tm -> elaborate tm >>= gets . flip whnf . typedTerm . unSpanned >>= print >> loop
          Show Bindings -> do
            scope <- get
            unless (Namespace.null scope) $ print scope
            loop
          Show Modules -> do
            ms <- gets @(ModuleGraph Core Void) (Map.toList . unModuleGraph)
            unless (Prelude.null ms) $ print (tabulate2 space (map (fmap (parens . pretty . modulePath . unScopeH)) ms))
            loop
          Reload -> reload *> loop
          Command.Import i -> do
            modify (Set.insert (unSpanned i))
            loop
          Command.Doc moduleName -> do
            m <- get >>= lookupModule moduleName
            case moduleDocs (unScopeH (m :: ScopeH Qualified (Module Core) Core Void)) of
              Just d  -> print (pretty d)
              Nothing -> print (pretty "no docs for" <+> squotes (pretty (unSpanned moduleName)))
            loop
        reload = do
          sorted <- traverse parseModule packageSources >>= renameModuleGraph >>= fmap (map (instantiateHEither (either pure absurd))) . loadOrder
          checked <- foldM (load (length packageSources)) (mempty @(ModuleGraph Core Void)) (zip [(1 :: Int)..] sorted)
          put checked
        load n graph (i, m) = skipDeps graph m $ do
          let name    = moduleName m
              ordinal = brackets (pretty i <+> pretty "of" <+> pretty n)
              path    = parens (pretty (modulePath m))
          print (ordinal <+> pretty "Compiling" <+> pretty name <+> path)
          table <- get
          (errs, (scope, res)) <- runState Nil (runReader (table :: ModuleTable) (runState (mempty :: Namespace.Namespace) (runReader graph (elabModule m))))
          if Prelude.null errs then do
            modify (Map.insert name scope)
            pure (ModuleGraph (Map.insert name (bindHEither Left res) (unModuleGraph graph)))
          else do
            for_ errs (print @Doc)
            pure graph
        skipDeps graph m action = if all @Set.Set (flip Set.member (Map.keysSet (unModuleGraph graph))) (Map.keysSet (moduleImports m)) then action else pure graph

elaborate :: (Carrier sig m, Effect sig, Member (Error Doc) sig, Member Naming sig, Member (State Namespace.Namespace) sig, Member (State (ModuleGraph Core Void)) sig, Member (State (Set.Set ModuleName)) sig) => Spanned (Surface.Surface User) -> m (Spanned (Core Qualified ::: Core Qualified))
elaborate = runSpanned $ \ tm -> do
  ty <- inferType
  runSubgraph (asks @(ModuleGraph Core Void) (fmap unScopeH . unModuleGraph) >>= for tm . rename >>= runNamespace . define ty . elab)

runSubgraph :: (Carrier sig m, Member (State (ModuleGraph Core Void)) sig, Member (State (Set.Set ModuleName)) sig) => ReaderC (ModuleGraph Core Void) m a -> m a
runSubgraph m = do
  imported <- get
  subgraph <- gets @(ModuleGraph Core Void) (Module.restrict imported)
  runReader subgraph m

basePackage :: Package
basePackage = Package
  { packageName        = "Base"
  , packageSources     =
      [ "src/Base/Bool.path"
      , "src/Base/Either.path"
      , "src/Base/Fin.path"
      , "src/Base/Fix.path"
      , "src/Base/Function.path"
      , "src/Base/Lazy.path"
      , "src/Base/List.path"
      , "src/Base/Maybe.path"
      , "src/Base/Nat.path"
      , "src/Base/Pair.path"
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
