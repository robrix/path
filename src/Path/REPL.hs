{-# LANGUAGE DeriveAnyClass, DeriveFunctor, DeriveGeneric, DerivingStrategies, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, RankNTypes, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.REPL where

import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Lift
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Writer
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
import Path.Error
import Path.Module as Module
import Path.Name
import Path.Package
import Path.Parser (Delta(..), parseString, whole)
import Path.Parser.Module (parseModule)
import Path.Parser.REPL (command)
import Path.Pretty
import Path.Problem
import Path.REPL.Command as Command
import Path.Scope
import Path.Span
import Path.Stack
import qualified Path.Surface as Surface
import Path.Term
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
runREPL prefs settings = runInputTWithPrefs prefs settings . runM . runReader (Line 0) . runREPLC

newtype REPLC m a = REPLC { runREPLC :: ReaderC Line (LiftC (InputT m)) a }
  deriving newtype (Applicative, Functor, Monad, MonadFix, MonadIO)

instance (Carrier sig m, MonadException m, MonadIO m) => Carrier (REPL :+: Lift (InputT m)) (REPLC m) where
  eff (L (Prompt prompt k)) = REPLC $ do
    str <- lift (lift (getInputLine (cyan <> prompt <> plain)))
    local increment (runREPLC (k str))
    where cyan = "\ESC[1;36m\STX"
          plain = "\ESC[0m\STX"
  eff (L (Print text k)) = putDoc text *> k
  eff (L (AskLine k)) = REPLC ask >>= k
  eff (R other) = REPLC (eff (R (handleCoercible other)))

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
       (script packageSources)))

newtype Line = Line Int64

increment :: Line -> Line
increment (Line n) = Line (n + 1)

lineDelta :: Line -> Delta
lineDelta (Line l) = Lines l 0 0 0

script :: ( Carrier sig m
          , Effect sig
          , Member REPL sig
          , MonadIO m
          )
       => [FilePath]
       -> m ()
script packageSources
  = evalState (ModuleGraph mempty :: ModuleGraph (Term (Problem :+: Core)) Void)
  . evalState (mempty @(Set.Set ModuleName))
  . runReader (ModuleName "(interpreter)")
  . runNaming
  $ runError loop >>= either (print @Doc) pure
  where loop = (prompt "λ: " >>= parseCommand >>= maybe loop runCommand . join)
          `catchError` (const loop <=< print @Doc)
        parseCommand str = do
          l <- askLine
          traverse (parseString (whole command) (lineDelta l)) str
        runCommand = \case
          Quit -> pure ()
          Help -> print helpDoc *> loop
          TypeOf tm -> elaborate tm >>= print . unSpanned >> loop
          Command.Decl decl -> runSubgraph (asks @(ModuleGraph (Term (Problem :+: Core)) Void) (fmap unScopeT . unModuleGraph) >>= flip renameDecl decl >>= inContext . elabDecl) >> loop
          Eval tm -> elaborate tm >>= gets . flip whnf . unSpanned >>= print >> loop
          ShowModules -> do
            ms <- gets @(ModuleGraph (Term (Problem :+: Core)) Void) (Map.toList . unModuleGraph)
            unless (Prelude.null ms) $ print (tabulate2 space (map (fmap (parens . pretty . modulePath . unScopeT)) ms))
            loop
          Reload -> reload *> loop
          Command.Import i -> do
            modify (Set.insert (unSpanned i))
            loop
          Command.Doc moduleName -> do
            m <- get >>= lookupModule moduleName
            case moduleDocs (unScopeT (m :: ScopeT Qualified Module (Term (Problem :+: Core)) Void)) of
              Just d  -> print (pretty d)
              Nothing -> print (pretty "no docs for" <+> squotes (pretty (unSpanned moduleName)))
            loop
        reload = do
          sorted <- traverse parseModule packageSources >>= renameModuleGraph >>= fmap (map (instantiateTEither (either pure absurd))) . loadOrder
          checked <- foldM (load (length packageSources)) (mempty @(ModuleGraph (Term (Problem :+: Core)) Void)) (zip [(1 :: Int)..] sorted)
          put checked
        load n graph (i, m) = skipDeps graph m $ do
          let name    = moduleName m
              ordinal = brackets (pretty i <+> pretty "of" <+> pretty n)
              path    = parens (pretty (modulePath m))
          print (ordinal <+> pretty "Compiling" <+> pretty name <+> path)
          (errs, res) <- runWriter @(Stack Doc) (runReader graph (elabModule m))
          if Prelude.null errs then
            pure (ModuleGraph (Map.insert name (bindTEither Left res) (unModuleGraph graph)))
          else do
            for_ errs print
            pure graph
        skipDeps graph m action = if all @Set.Set (flip Set.member (Map.keysSet (unModuleGraph graph))) (Map.keysSet (moduleImports m)) then action else pure graph

elaborate :: ( Carrier sig m
             , Effect sig
             , Member (Error Doc) sig
             , Member Naming sig
             , Member (State (ModuleGraph (Term (Problem :+: Core)) Void)) sig
             , Member (State (Set.Set ModuleName)) sig
             )
          => Spanned (Term Surface.Surface User)
          -> m (Spanned (Term (Problem :+: Core) Qualified))
elaborate = runSpanned $ \ tm -> do
  ty <- meta type'
  tm' <- runSubgraph (asks @(ModuleGraph (Term (Problem :+: Core)) Void) (fmap unScopeT . unModuleGraph) >>= for tm . rename >>= inContext . goalIs ty . elab)
  either freeVariables pure (strengthen tm')

-- | Evaluate a term to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: ModuleGraph (Term (Problem :+: Core)) Void -> Term (Problem :+: Core) Qualified -> Term (Problem :+: Core) Qualified
whnf graph = go where
  go (Term (R (Var n :$ a))) = maybe (Var n $$ a) (go . ($$ a) . unSpanned . declTerm) (Module.lookup n graph)
  go v                       = v

runSubgraph :: (Carrier sig m, Member (State (ModuleGraph (Term (Problem :+: Core)) Void)) sig, Member (State (Set.Set ModuleName)) sig) => ReaderC (ModuleGraph (Term (Problem :+: Core)) Void) m a -> m a
runSubgraph m = do
  imported <- get
  subgraph <- gets @(ModuleGraph (Term (Problem :+: Core)) Void) (Module.restrict imported)
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
