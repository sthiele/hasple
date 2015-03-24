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
   heads_p, atoms_p,      
  ) where
    
import Data.List (nub)                  
import Data.Maybe 
-- --------------------------------------------------------------

data Term = Constant Integer
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
                 }deriving (Eq, Ord)

showlist :: (Show a) => [a] -> String
showlist [] = ""
showlist (x:[]) = (show x)
showlist (x:xs) = (show x)  ++ "," ++ (showlist xs)                 
                 
instance Show Atom where
    show (Atom pred []) =  pred
    show (Atom pred xs) =  pred ++"("++showlist xs++")"
    

__conflict = (Atom "conflict" [])


-- --------------------------------------------------------------

data Rule = Rule { kopf :: Atom
                 , pbody :: [Atom]
                 , nbody :: [Atom]
                 }

shownbody :: [Atom] -> String
shownbody [] = ""
shownbody (x:[]) = "not " ++ (show x)
shownbody (x:xs) = "not " ++ (show x) ++ ", "++ (shownbody xs)

instance Show Rule where
  show (Rule h [] []) =  (show h) ++"."
  show (Rule h pb []) =  (show h) ++ " :- "++showlist pb++"."
  show (Rule h [] nb) =  (show h) ++ " :- "++shownbody nb++"."
  show (Rule h pb nb) =  (show h) ++ " :- "++(showlist pb)++", "++(shownbody nb)++"."

instance Eq Rule where
  (Rule h1 pb1 nb1) == (Rule h2 pb2 nb2) = h1==h2 && pb1==pb2 && nb1==nb2

instance Ord Rule where
  compare (Rule h pb nb) (Rule h2 pb2 nb2) = compare h h2


heads_p :: [Rule] -> [Atom]
-- returns the head of all rules without the contradiction symbol "" (all consistent consequences)
heads_p rules =
  filter (\i -> i/=__conflict )
  (nub (map kopf rules))

atoms_p :: [Rule] -> [Atom]
-- returns the atoms of all rules without the contradiction symbol 
atoms_p rules =
  filter (\i -> i/=__conflict )
  (nub (map kopf rules)++ (concatMap pbody rules) ++ (concatMap pbody rules))  