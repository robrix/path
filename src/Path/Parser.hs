{-# LANGUAGE DeriveGeneric, DeriveTraversable, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Parser
( parseFile
, parseString
, whole
, identifier
, reservedWords
, keyword
, op
) where

import Control.Applicative (Alternative(..))
import Control.Carrier.Parser.Church
import qualified Data.HashSet as HashSet
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
