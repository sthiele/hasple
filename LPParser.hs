-- Copyright (c) 2014, Sven Thiele <sthiele78@gmail.com>

-- This file is part of hasple.

-- hasple is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.

-- hasple is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.

-- You should have received a copy of the GNU General Public License
-- along with hasple.  If not, see <http://www.gnu.org/licenses/>.

module LPParser (
    readProgram
  ) where

import ASP
import Text.ParserCombinators.Parsec
import qualified Text.Parsec.Token as Token
import Text.ParserCombinators.Parsec.Language (emptyDef)

-- the lexer bzw tokenizer

myLangDef = emptyDef{
--                 P.commentStart = "{-"
--               , P.commentEnd = "-}"
                Token.commentLine     = "%"
              , Token.identStart      = lower
              , Token.identLetter     = alphaNum
--               , P.opStart = oneOf "~&=:"
--               , P.opLetter = oneOf "~&=:"
              , Token.reservedOpNames = [":-", "==", "!=", ".", ","]
              , Token.reservedNames   = ["not", "false", "true"]
              , Token.caseSensitive   = True
              }

lexer       = Token.makeTokenParser myLangDef

identifier  = Token.identifier lexer
negationp   = Token.reserved lexer "not"
ifparser    = Token.reservedOp lexer ":-"
dotparser   = Token.reservedOp lexer "."
commaparser = Token.reservedOp lexer ","
parens      = Token.parens lexer
commaSep    = Token.commaSep lexer
integer     = Token.integer lexer
whiteSpace  = Token.whiteSpace lexer
-- semi        = Token.semi lexer


-- the parser


alphaNumUnderScore :: Parser Char
alphaNumUnderScore = alphaNum <|> char '_'


--------
readAtom input =  parse parseAtom "atom" input

parseAtom :: Parser Atom
parseAtom =
  do
    p <- identifier
    a <- parseArguments
    return (Atom p a)
            
parseArguments :: Parser [Term]
parseArguments = (parens (commaSep parseArg))
  <|>
  do return []

parseArg =  choice [parseVar, parseIndent, parseConst]
-- parseArg2 = choice [parseVar, identifier, integer]

parseVar = 
  do
    firstChar <- upper
    restChars <- many alphaNumUnderScore
    whiteSpace
    return (Variable (firstChar : restChars))
                          
parseIndent = 
  do
    p <- identifier
    return (Identifier p)

parseConst =
  do
    n <- integer
    return (Constant n)


-------------
readLit input = 
  case parse parseLit "lit" input of
    Left err  -> "No match: " ++ show err
    Right val -> "Found value " ++ show val



parseLit :: Parser Literal
parseLit =  
 parsenAtom <|> parsepAtom         


parsepAtom :: Parser Literal
parsepAtom = 
  do
    atom <- parseAtom
    return (PAtom atom)
               

parsenAtom :: Parser Literal
parsenAtom =
  do
    negationp
    atom <- parseAtom
    return (NAtom atom )


--------------
readrule input =  parse parseRule "rul" input

parseRule :: Parser Rule
parseRule = 
  do
    ifparser
    lits <- parseBody2
    return (Rule __conflict  lits)
  <|>
  do
      head <- parseAtom
      lits <- parseBody
      return (Rule head lits)

parseBody = 
  do
    dotparser
    return []
  <|>
  do
    ifparser
    ret <- parseLitList
    dotparser
    return ret

parseBody2 = 
  do
   dotparser
   return []
  <|>
  do
    ret <- parseLitList
    dotparser
    return ret              

parseLitList :: Parser [Literal]
parseLitList = 
  do
    stmts <- sepEndBy1 parseLit (commaparser)
    return $! stmts

                   
                   
-----------                   
readProgram input =  parse parseProgram "prg" input
                
parseProgram ::  Parser [Rule]
parseProgram = 
  do
    spaces
    x <- (many1 parseRule)
    eof
    return x






