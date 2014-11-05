-- Copyright (c) 2014, Sven Thiele <sthiele78@gmail.com>

-- This file is part of hasple.

-- hasple is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.

-- hasple is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.

-- You should have received a copy of the GNU General Public License
-- along with hasple.  If not, see <http://www.gnu.org/licenses/>.

module LPparser (
    readPrg
  ) where

-- import Data.List (sort)
import ASP
import Text.ParserCombinators.Parsec
import qualified Text.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (emptyDef)


data Literal = Literal { sign' :: Bool
                 , atom' :: Atom
                 }
ispos :: Literal -> Bool
ispos (Literal True atom) = True
ispos (Literal False atom) = False

getatom :: Literal -> Atom
getatom (Literal b atom) = atom


instance Show Literal where
  show (Literal True atom) =  atom
  show (Literal False atom) =  "NoT " ++ atom



-- the lexer bzw tokenizer


myLangDef = emptyDef{
--                 P.commentStart = "{-"
--               , P.commentEnd = "-}"
              P.commentLine = "%"
              , P.identStart = lower
              , P.identLetter = alphaNum
--               , P.opStart = oneOf "~&=:"
--               , P.opLetter = oneOf "~&=:"
              , P.reservedOpNames = [":-", "==", "!=", ".", ","]
              , P.reservedNames = ["not", "false", "true"]
              , P.caseSensitive = True
              }


lexer = P.makeTokenParser myLangDef

identifier = P.identifier lexer
negationp  = P.reserved lexer "not"
ifparser   = P.reservedOp lexer ":-"
dotparser   = P.reservedOp lexer "."
commaparser   = P.reservedOp lexer ","
semi = P.semi lexer


-- the parser

parseAtom :: Parser Atom
parseAtom =  identifier


parsepAtom :: Parser Literal
parsepAtom = do
              atom <- parseAtom
              return (Literal True atom)


parsenAtom :: Parser Literal
parsenAtom = do
                negationp
                atom <- parseAtom
                return (Literal False atom )


parseLit :: Parser Literal
parseLit =  parsenAtom
         <|> parsepAtom

readLit input = case parse parseLit "lit" input of
    Left err -> "No match: " ++ show err
    Right val -> "Found value " ++ show val



parseBody = do
              dotparser
              return []
            <|>
            do
              ifparser
              ret <- parseLitList
              dotparser
              return ret


parseLitList  :: Parser [Literal]
parseLitList  = do
                  stmts <- sepEndBy1 parseLit (commaparser)
                  return $! stmts

posbody :: [Literal] -> [Atom]
posbody [] = []
posbody (l:t) = if ispos l
                   then ((getatom l):(posbody t))
                   else (posbody t)

negbody :: [Literal] -> [Atom]
negbody [] = []
negbody (l:t) = if ispos l
                   then (negbody t)
                   else ((getatom l):(negbody t))

parseRule :: Parser Rule
parseRule =  do
                head <- parseAtom
                lits <- parseBody
                return (Rule head (posbody lits) (negbody lits))

readRule input = case parse parseRule "rule" input of
    Left err -> "No match: " ++ show err
    Right val -> "Found value " ++ show val



parseProgramm::  Parser [Rule]
parseProgramm = many parseRule


readPrg input = case parse parseProgramm "prg" input of
    Left err -> "No match: " ++ show err
    Right val -> "Found value " ++ show val




