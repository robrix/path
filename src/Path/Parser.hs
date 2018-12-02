{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Parser where

import Control.Applicative (Alternative(..))
import Control.Monad.IO.Class
import Control.Monad (MonadPlus(..))
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace)
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.LookAhead
import Text.Parser.Token
import Text.Parser.Token.Style
import qualified Text.Trifecta as Trifecta
import Text.Trifecta.Delta
import Text.Trifecta.Indentation

type Parser = IndentationParserT Char Inner
-- type MonadParsing m = (IndentationParsing m, Monad m, TokenParsing m)

newtype Inner a = Inner { runInner :: Trifecta.Parser a }
  deriving (Alternative, Applicative, CharParsing, Trifecta.DeltaParsing, Functor, LookAheadParsing, Trifecta.MarkParsing Delta, Monad, MonadPlus, Parsing)

instance TokenParsing Inner where
  someSpace = Inner $ buildSomeSpaceParser (skipSome (satisfy isSpace)) haskellCommentStyle
  nesting = Inner . nesting . runInner
  highlight h = Inner . highlight h . runInner


parseFile :: MonadIO m => Parser a -> FilePath -> m (Maybe a)
parseFile p = Trifecta.parseFromFile (runInner (whiteSpace *> evalIndentationParserT p indentst))

parseString :: Parser a -> String -> Either String a
parseString p = toResult . Trifecta.parseString (runInner (evalIndentationParserT p indentst)) directed

toResult :: Trifecta.Result a -> Either String a
toResult r = case r of
  Trifecta.Success a -> Right a
  Trifecta.Failure info -> Left (show (Trifecta._errDoc info))


directed :: Delta
directed = Directed BS.empty 0 0 0 0

indentst :: IndentationState
indentst = mkIndentationState 0 infIndentation True Gt

whole :: TokenParsing m => m a -> m a
whole p = whiteSpace *> p <* eof
