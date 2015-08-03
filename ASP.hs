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
   Term(..),
   Atom(..),
   __conflict,
   Literal(..),
   Rule(..),
   basicRule,
   normalRule,
   pbody,
   nbody,
   heads_p,
   atoms_p,
) where
    
import Data.List (nub)                  
-- --------------------------------------------------------------

data Term = Constant Integer
          | Identifier String
          | Variable String
          | Addition Term Term
          | Subtraction Term Term
          | Multiplication Term Term
--           | Division Term Term
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
showlist [x] = show x
showlist (x:xs) = show x  ++ "," ++ showlist xs
                 
instance Show Atom where
    show (Atom pred []) =  pred
    show (Atom pred xs) =  pred ++ "(" ++ showlist xs ++ ")"
    

__conflict = Atom "conflict" []


data Literal = PAtom Atom | NAtom Atom deriving (Eq, Ord) -- asp literal
instance Show Literal where
    show (PAtom a) =  show a
    show (NAtom a) =  "not " ++ show a

-- --------------------------------------------------------------

data Rule = Rule { kopf :: Atom
                 , body :: [Literal]
                 }

basicRule :: Atom -> [Atom] -> Rule
-- creates a basic rule 
basicRule h a = Rule h (fmap PAtom a)

normalRule :: Atom -> [Atom] -> [Atom] -> Rule
-- creates a normal rule
normalRule h pa na = Rule h ((fmap PAtom pa) ++ (fmap NAtom na))

instance Show Rule where
  show (Rule h []) = show h ++ "."
  show (Rule h body) = show h ++ " :- " ++ showlist body ++ "."
  
instance Eq Rule where
  (Rule h1 b1) == (Rule h2 b2) = h1==h2 && b1==b2
  
instance Ord Rule where
  compare (Rule h b1) (Rule h2 b2) = compare h h2


pbody :: Rule -> [Atom]
-- returns the positive body atoms of a rule
pbody (Rule _ body) = [ a | (PAtom a) <- body]

nbody :: Rule -> [Atom]
-- returns the negative body atoms of a rule
nbody (Rule _ body) = [ a | (NAtom a) <- body]


heads_p :: [Rule] -> [Atom]
-- returns the head of all rules without the contradiction symbol "" (all consistent consequences)
heads_p rules =
  filter (\i -> i/=__conflict ) (nub (map kopf rules))

atoms_p :: [Rule] -> [Atom]
-- returns the atoms of all rules without the contradiction symbol 
atoms_p rules =
  filter (\i -> i/=__conflict) (nub (map kopf rules)++ (concatMap pbody rules) ++ (concatMap nbody rules))

