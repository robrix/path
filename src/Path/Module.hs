{-# LANGUAGE FlexibleContexts #-}
module Path.Module where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.NonDet
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad (unless, when)
import Data.Foldable (for_)
import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid (Alt(..))
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc
import Path.Decl
import Path.Surface
import Path.Term

data ModuleName
  = ModuleName String
  | ModuleName :. String
  deriving (Eq, Ord, Show)

infixl 5 :.

instance Pretty ModuleName where
  pretty (ModuleName s) = pretty s
  pretty (ss :. s) = pretty ss <> dot <> pretty s

makeModuleName :: NonEmpty String -> ModuleName
makeModuleName (s:|ss) = foldl (:.) (ModuleName s) ss

data Module a = Module
  { moduleName    :: ModuleName
  , moduleImports :: [Import]
  , moduleDecls   :: [Decl a]
  }
  deriving (Eq, Ord, Show)

newtype Import = Import { importModuleName :: ModuleName }
  deriving (Eq, Ord, Show)


newtype ModuleGraph a = ModuleGraph { unModuleGraph :: Map.Map ModuleName (Module a) }
  deriving (Eq, Ord, Show)

moduleGraph :: [Module a] -> ModuleGraph a
moduleGraph = ModuleGraph . Map.fromList . map ((,) . moduleName <*> id)

lookupModule :: (Carrier sig m, Member (Error ModuleError) sig, Member (Reader (ModuleGraph (Term Surface))) sig, Monad m) => ModuleName -> m (Module (Term Surface))
lookupModule name = ask >>= maybe (throwError (UnknownModule name)) ret . Map.lookup name . unModuleGraph

cycleFrom :: (Carrier sig m, Effect sig, Member (Error ModuleError) sig, Member (Reader (ModuleGraph (Term Surface))) sig, Monad m) => ModuleName -> m ()
cycleFrom m = runReader (Set.empty :: Set.Set ModuleName) (runNonDetOnce (go m)) >>= throwError . CyclicImport . fromMaybe (m :| [])
  where go n = do
          inPath <- asks (Set.member n)
          if inPath then do
            m <- lookupModule n
            (n <|) <$> local (Set.insert (moduleName m)) (getAlt (foldMap (Alt . go . importModuleName) (moduleImports m)))
          else
            pure (n :| [])

data ModuleError
  = UnknownModule ModuleName
  | CyclicImport (NonEmpty ModuleName)
  deriving (Eq, Ord, Show)

instance Pretty ModuleError where
  pretty (UnknownModule name) = hsep (map pretty (words "Could not find module") <> [squotes (pretty name)])
  pretty (CyclicImport (name :| [])) = nest 2 (vsep
    [ hsep (map pretty (words "Module imports form a cycle:"))
    , hsep [ pretty "module", squotes (pretty name), pretty "imports", pretty "itself" ]
    ])
  pretty (CyclicImport (name :| name' : names)) = nest 2 (vsep
    ( hsep (map pretty (words "Module imports form a cycle:"))
    : hsep [ pretty "       module", squotes (pretty name) ]
    : hsep [ pretty "      imports", squotes (pretty name') ]
    : foldr ((:) . whichImports) [ whichImports name ] names
    ))
    where whichImports name = fillSep [ pretty "which imports", squotes (pretty name) ]


loadOrder :: ModuleGraph (Term Surface) -> Either ModuleError [Module (Term Surface)]
loadOrder g = reverse <$> run (runError (execState [] (evalState (Set.empty :: Set.Set ModuleName) (runReader g (runReader (Set.empty :: Set.Set ModuleName) (for_ (Map.keys (unModuleGraph g)) loop))))))
  where loop n = do
          inPath <- asks (Set.member n)
          when inPath (cycleFrom n)
          visited <- gets (Set.member n)
          unless visited . local (Set.insert n) $ do
            m <- lookupModule n
            for_ (moduleImports m) (loop . importModuleName)
            modify (Set.insert n)
            modify (m :)
