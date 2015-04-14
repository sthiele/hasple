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

module Grounder (
   groundProgram,
   matchAtom,
   AtomMap,
   emptyAtomMap,
   insert_atoms,
   groundRule,
   groundRule2,     
) where
  
import ASP
import Data.List (sort, nub, intersect, (\\), delete )
import Data.Maybe
-- import Data.List.Extra (nubOrd)
-- use sort to order list nub (nubOrd) to remove duplicates from list -- maybe use Sets instead?
import qualified Data.Set as Set
import qualified Data.Map as Map

type AtomMap =  Map.Map (String, Int) (Set.Set [Term])
emptyAtomMap:: AtomMap
emptyAtomMap = Map.empty

insert_atom:: AtomMap -> (String, Int) -> [Term] -> AtomMap
-- insert an atom (pred/2 [args]) into the atom map
insert_atom am key val =
    case Map.lookup key am of
      Nothing -> Map.insert key (Set.insert val Set.empty) am
      Just x  -> Map.insert key (Set.insert val x) am

insert_atoms:: AtomMap -> [Atom] -> AtomMap
-- insert a list of atoms into the atom map
insert_atoms am [] = am
insert_atoms am ((Atom pred args):xs) =
  let am2 = insert_atom am (pred, (length args)) args
  in
  insert_atoms am2 xs


matchTerm:: Term -> Term -> Maybe [(Term,Term)]
-- can two terms be unified if yes return variable bindings
matchTerm (Identifier x) (Constant y) = Nothing
matchTerm (Constant x) (Identifier y) = Nothing
matchTerm (Constant x) (Constant y) =
  if x==y
     then Just []
     else Nothing
matchTerm (Identifier x) (Identifier y) =
  if x==y
     then Just []
     else Nothing

matchTerm (Variable x) (Identifier y) = Just [ ((Variable x),(Identifier y))]
matchTerm (Variable x) (Constant y) = Just [ ((Variable x),(Constant y))]
matchTerm (Addition x y) (Constant z) = Just []
matchTerm (Addition x y) (Identifier z) = Nothing
matchTerm (Subtraction x y) (Constant z) = Just []
matchTerm (Subtraction x y) (Identifier z) = Nothing
matchTerm (Multiplication x y) (Constant z) = Just []
matchTerm (Multiplication x y) (Identifier z) = Nothing
matchTerm (Negation x) (Constant z) = Just []
matchTerm (Negation x) (Identifier z) = Nothing
matchTerm (Variable x) (Variable y) = Just [((Variable x),(Variable y))]
matchTerm x y = Just [(x,(Identifier ("Whaaat????"++ show y)))]


match:: [Term] -> [Term] -> Maybe [(Term,Term)]
-- can two argumentlist be unified if yes return variable bindings
match [] [] = Just []
match (x:xs) (y:ys) =
  if (length xs) == (length ys)
     then
     case (matchTerm x y) of
          Nothing -> Nothing
          Just [] ->  (match xs ys)
          Just [(var,const)] -> join (var,const) (match xs ys)
     else Nothing
match _ _ = Nothing

matchAtom:: Atom -> Atom -> Maybe [(Term,Term)]
matchAtom (Atom p1 a1) (Atom p2 a2) =
  if p1==p2
  then match a1 a2
  else Nothing



join:: (Term,Term) -> Maybe [(Term,Term)] -> Maybe [(Term,Term)]
join x Nothing = Nothing
join x (Just []) = Just [x]
join (v, c) (Just list) =
      case lookup v list of
           Nothing -> (Just ((v,c):list))
           Just (Variable v2) -> Just list
           Just x -> if x==c
                        then Just list
                        else Nothing


getbindings:: Atom -> AtomMap -> [[(Term,Term)]]
-- return the possible variable bindings associated a non ground atom
getbindings  (Atom pred args) m =
  let x = Map.lookup (pred, (length args)) m in
      case x of
           Nothing -> [[]]
           Just z ->  (getbindings2 args (Set.toList z))

getbindings2:: [Term] -> [[Term]] ->  [[(Term,Term)]]
getbindings2 x [] = []
getbindings2 x (y:ys) =
  case (match x y) of
       Nothing -> (getbindings2 x ys)
       Just z -> z:(getbindings2 x ys)


getbindingsAtoms:: [Atom] -> AtomMap -> [[(Term,Term)]]
getbindingsAtoms [] m = [[]]
getbindingsAtoms (x:xs) m = join2 (getbindings x m) (getbindingsAtoms xs m)

join2:: [[(Term,Term)]] -> [[(Term,Term)]] -> [[(Term,Term)]]
-- join2 xs ys = [ z | x <- xs, y <- ys, (merge x y)==(Just z)]
join2 [] ys = []
join2 xs [] = []
join2 xs ys =
  do
    x <- xs
    y <- ys
    case (merge x y) of
         Just z -> return z
         Nothing -> []


merge:: [(Term,Term)] -> [(Term,Term)] -> Maybe [(Term,Term)]
merge [] ys = Just ys
merge (x:xs) ys =
  case (merge2 x ys) of
       Nothing -> Nothing
       Just z -> merge xs z


merge2:: (Term,Term) -> [(Term,Term)] -> Maybe [(Term,Term)]
merge2 (k,v) ys =
  case lookup k ys of
       Nothing -> Just ((k,v):ys)
       Just z -> if v==z
                 then (Just ys)
                 else Nothing


-- --------------------------------------------------------------

subsTerm:: [(Term,Term)] -> Term -> Term
subsTerm m (Constant x) = (Constant x)
subsTerm m (Identifier x) = (Identifier x)
subsTerm m (Variable x) =
              case lookup (Variable x) m of
                Just y -> y
                Nothing -> (Variable x)

subsTerm m (Addition x y) =
  let xsubs = subsTerm m x
      ysubs = subsTerm m y
  in
  (Addition xsubs ysubs)

subsTerm m (Subtraction x y) =
  let xsubs = subsTerm m x
      ysubs = subsTerm m y
  in
  (Subtraction xsubs ysubs)

subsTerm m (Multiplication x y) =
  let xsubs = subsTerm m x
      ysubs = subsTerm m y
  in
  (Multiplication xsubs ysubs)

subsTerm m (Negation x) =
  let xsubs = subsTerm m x in
  (Negation xsubs)



subsAtom:: [(Term,Term)] -> Atom -> Atom
subsAtom m (Atom pred []) = (Atom pred [])
subsAtom m (Atom pred x)  = (Atom pred (map (subsTerm m) x))

subsLit:: [(Term,Term)] -> Literal -> Literal
subsLit m (PAtom a) = (PAtom (subsAtom m a) )
subsLit m (NAtom a) = (NAtom (subsAtom m a))

groundRule2:: Rule -> [(Term,Term)] -> Rule
groundRule2 (Rule h b) m= (Rule (subsAtom m h) (map (subsLit m) b) )


-- alternative
groundRule:: AtomMap ->  Rule -> [Rule]
groundRule am r =
  if (is_groundRule r)
  then [r]
  else
    let c =  getbindingsAtoms (pbody r) am in
    nub (map (groundRule2 r) c)


groundProgram:: [Rule] -> [Rule]
groundProgram p =
  let am = insert_atoms emptyAtomMap (heads_p  p)
      pg1 = nub (concatMap  (groundRule am)  p)
  in
  if pg1==p
  then pg1
  else groundProgram pg1



is_groundRule:: Rule -> Bool
-- return true if a rule does not contain variables
is_groundRule (Rule h b) = is_groundAtom h && is_groundLits b

is_groundLits:: [Literal] -> Bool
-- returns true if the literals do not contain variables
is_groundLits [] = True
is_groundLits (x:xs) = is_groundLit x && is_groundLits xs

is_groundLit:: Literal -> Bool
-- returns true if the literal does not contain variables
is_groundLit (PAtom a) = is_groundAtom a
is_groundLit (NAtom a) = is_groundAtom a


is_groundAtom:: Atom -> Bool
-- returns true if the atom does not contain variables
is_groundAtom (Atom pred args) = is_groundTerms args

is_groundTerms:: [Term] -> Bool
-- returns true if the list of Terms only consists of constants
is_groundTerms [] = True
is_groundTerms ((Constant x):xs) = is_groundTerms xs
is_groundTerms ((Identifier x):xs) = is_groundTerms xs
is_groundTerms _ = False
