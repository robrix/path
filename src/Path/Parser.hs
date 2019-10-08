{-# LANGUAGE DeriveGeneric, DeriveTraversable, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Parser
( parseFile
, parseString
, whole
, keyword
, identifier
, reservedWords
, op
, spanned
) where

import Control.Applicative (Alternative(..))
import Control.Carrier.Parser.Church
import Control.Effect.Carrier
import Control.Effect.Reader
import qualified Data.HashSet as HashSet
import Path.Span hiding (spanned)
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token
import Text.Parser.Token.Highlight

whole :: TokenParsing m => m a -> m a
whole p = whiteSpace *> p <* eof


identifier :: (Monad m, TokenParsing m) => m String
identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier)


reservedWords :: HashSet.HashSet String
reservedWords = HashSet.fromList [ "Type", "module", "import" ]

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s


path :: (Carrier sig m, Member (Reader FilePath) sig) => m FilePath
path = ask

spanned :: (Carrier sig m, Member (Reader [String]) sig, Member (Reader FilePath) sig, Member Parser sig) => m a -> m (Spanned a)
spanned m = do
  path <- path
  line <- line
  start <- position
  a <- m
  end <- position
  pure (a :~ Excerpt path line (Span start end))
