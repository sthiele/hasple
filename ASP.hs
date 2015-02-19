-- Copyright (c) 2015, Sven Thiele <sthiele78@gmail.com>

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

module ASP (
    Term(..), Atom(..), __conflict, Rule(..),
  ) where
                  
 
-- --------------------------------------------------------------

data Term = Constant Int
                | Identifier String
                | Variable String
                | Addition Term Term
                | Subtraction Term Term
                | Multiplication Term Term
--                 | Division Term Term
                | Negation Term
                deriving (Eq, Ord)
                
instance Show Term where
  show (Identifier x) = x
  show (Variable x) = x
  show (Constant x) = show x

  
-- --------------------------------------------------------------

data Atom = Atom { predicate :: String
                 , arguments :: [Term]
                 }

showlist :: (Show a) => [a] -> String
showlist [] = ""
showlist (x:[]) = (show x)
showlist (x:xs) = (show x)  ++ "," ++ (showlist xs)                 
                 
instance Show Atom where
    show (Atom pred []) =  pred
    show (Atom pred xs) =  pred ++"("++showlist xs++")"
    
instance Eq Atom where
  (Atom p1 args1) == (Atom p2 args2) = p1==p2 && args1==args2

instance Ord Atom where
  compare (Atom pred args) (Atom pred2 args2) = compare pred pred2

__conflict = (Atom "conflict" [])


-- --------------------------------------------------------------

data Rule = Rule { kopf :: Atom
                 , pbody :: [Atom]
                 , nbody :: [Atom]
                 }

shownbody :: [Atom] -> String
shownbody [] = ""
shownbody (x:[]) = "not " ++ (show x)
shownbody (x:xs) =  "not " ++ (show x) ++ ", "++ (shownbody xs)

instance Show Rule where
  show (Rule h [] []) =  (show h) ++"."
  show (Rule h pb []) =  (show h) ++ " :- "++showlist pb++"."
  show (Rule h [] nb) =  (show h) ++ " :- "++shownbody nb++"."
  show (Rule h pb nb) =  (show h) ++ " :- "++(showlist pb)++", "++(shownbody nb)++"."

instance Eq Rule where
  (Rule h1 pb1 nb1) == (Rule h2 pb2 nb2) = h1==h2 && pb1==pb2 && nb1==nb2

instance Ord Rule where
  compare (Rule h pb nb) (Rule h2 pb2 nb2) = compare h h2

          