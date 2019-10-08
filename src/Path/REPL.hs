{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, RankNTypes, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.REPL where

import Control.Carrier.Readline.Haskeline
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Lift
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Writer
import Control.Monad (foldM, join, unless, void)
import Control.Monad.IO.Class
import Data.Foldable (for_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void
import Path.Core
import Path.Elab
import Path.Error
import Path.Module as Module
import Path.Name
import Path.Package
import Path.Parser (parseString, whole)
import Path.Parser.Module (parseModule)
import Path.Parser.REPL (command)
import Path.Pretty
import Path.REPL.Command as Command
import Path.Scope
import Path.Span
import qualified Path.Surface as Surface
import Prelude hiding (print)
import Syntax.Stack
import Syntax.Term
import Syntax.Trans.Scope
import Syntax.Var
import System.Console.Haskeline hiding (Handler, handle)
import System.Directory (createDirectoryIfMissing, getHomeDirectory)
import Syntax.Vec

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
  runM (runReadline prefs settings
       (script packageSources))

script :: ( Carrier sig m
          , Effect sig
          , Member Readline sig
          , MonadIO m
          )
       => [FilePath]
       -> m ()
script packageSources
  = evalState (ModuleGraph mempty :: ModuleGraph (Term Core) Void)
  . evalState (mempty @(Set.Set ModuleName))
  . runReader (ModuleName "(interpreter)")
  . fmap (either id id)
  . runError @()
  $ runError loop >>= either (print . pretty @Notice) pure
  where loop = (prompt "λ: " >>= uncurry parseCommand >>= maybe (pure ()) runCommand . join) `catchError` (print . pretty @Notice) >> loop
        parseCommand l = traverse (parseString (whole command) (linePos l))
        runCommand = \case
          Quit -> throwError ()
          Help -> print helpDoc
          TypeOf tm -> elaborate tm >>= print . pretty . unSpanned
          Command.Decl decl -> void $ runSubgraph (asks @(ModuleGraph (Term Core) Void) (fmap unScopeT . unModuleGraph) >>= flip renameDecl decl >>= withGlobals . elabDecl)
          Eval tm -> elaborate tm >>= gets . flip whnf . unSpanned >>= print . pretty
          ShowModules -> do
            ms <- gets @(ModuleGraph (Term Core) Void) (Map.toList . unModuleGraph)
            unless (Prelude.null ms) $ print (tabulate2 space (map (fmap (parens . pretty . modulePath . unScopeT)) ms))
          Reload -> reload
          Command.Import i -> modify (Set.insert (unSpanned i))
          Command.Doc moduleName -> do
            m <- get >>= lookupModule moduleName
            print $ case moduleDocs (unScopeT (m :: ScopeT Qualified Module (Term Core) Void)) of
              Just d  -> pretty d
              Nothing -> pretty "no docs for" <+> squotes (pretty (unSpanned moduleName))
        reload = do
          sorted <- traverse parseModule packageSources >>= renameModuleGraph >>= fmap (map (instantiateVarT (unVar pure absurd))) . loadOrder
          checked <- foldM (load (length packageSources)) (mempty @(ModuleGraph (Term Core) Void)) (zip [(1 :: Int)..] sorted)
          put checked
        load n graph (i, m) = skipDeps graph m $ do
          let name    = moduleName m
              ordinal = brackets (pretty i <+> pretty "of" <+> pretty n)
              path    = parens (pretty (modulePath m))
          print (ordinal <+> pretty "Compiling" <+> pretty name <+> path)
          (errs, res) <- runWriter (runReader graph (elabModule m))
          if Prelude.null errs then
            pure (ModuleGraph (Map.insert name (abstractVarT B res) (unModuleGraph graph)))
          else do
            for_ @Stack errs (print . pretty @Notice)
            pure graph
        skipDeps graph m action = if all @Set.Set (flip Set.member (Map.keysSet (unModuleGraph graph))) (Map.keysSet (moduleImports m)) then action else pure graph

elaborate :: ( Carrier sig m
             , Effect sig
             , Member (Error Notice) sig
             , Member (State (ModuleGraph (Term Core) Void)) sig
             , Member (State (Set.Set ModuleName)) sig
             )
          => Spanned (Surface.Surface User)
          -> m (Spanned (Term Core Qualified))
elaborate = runSpanned $ \ tm -> strengthen <$> do
  let ty = meta type'
  runSubgraph (asks @(ModuleGraph (Term Core) Void) (fmap unScopeT . unModuleGraph) >>= for tm . rename >>= withGlobals . goalIs ty . elab VZ . fmap F >>= solve VZ)

-- | Evaluate a term to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: ModuleGraph (Term Core) Void -> Term Core Qualified -> Term Core Qualified
whnf graph = go where
  go (Alg (Var n :$ a)) = maybe (Var n $$ a) (go . ($$ a) . unSpanned . declTerm) (Module.lookup n graph)
  go v                   = v

runSubgraph :: (Carrier sig m, Member (State (ModuleGraph (Term Core) Void)) sig, Member (State (Set.Set ModuleName)) sig) => ReaderC (ModuleGraph (Term Core) Void) m a -> m a
runSubgraph m = do
  imported <- get
  subgraph <- gets @(ModuleGraph (Term Core) Void) (Module.restrict imported)
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
