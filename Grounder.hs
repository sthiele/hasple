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
  applySubs
) where
  
import ASP
import Data.List (sort, nub, intersect, (\\), delete )
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map


type AtomMap =  Map.Map (String, Int) (Set.Set [Term])

emptyAtomMap :: AtomMap
emptyAtomMap = Map.empty

insert_atom :: AtomMap -> (String, Int) -> [Term] -> AtomMap
-- insert an atom (pred/2 [args]) into the atom map
insert_atom am key val =
  case Map.lookup key am of
    Nothing -> Map.insert key (Set.insert val Set.empty) am
    Just x  -> Map.insert key (Set.insert val x) am


insert_atoms :: AtomMap -> [Atom] -> AtomMap
-- insert a list of atoms into the atom map
insert_atoms am [] = am
insert_atoms am ((Atom pred args):xs) =
  let am2 = insert_atom am (pred, (length args)) args in
  insert_atoms am2 xs


matchTerm :: Term -> Term -> Maybe [(Term,Term)]
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


match :: [Term] -> [Term] -> Maybe [(Term,Term)]
-- can two argumentlist be unified if yes return variable bindings
match [] [] = Just []
match (x:xs) (y:ys) =
  if (length xs) == (length ys)
  then
    case (matchTerm x y) of
      Nothing            -> Nothing
      Just []            -> match xs ys
      Just [(var,const)] -> join (var,const) (match xs ys)
  else Nothing
match _ _ = Nothing


matchAtom :: Atom -> Atom -> Maybe [(Term,Term)]
matchAtom (Atom p1 a1) (Atom p2 a2) =
  if p1==p2
  then match a1 a2
  else Nothing


join :: (Term,Term) -> Maybe [(Term,Term)] -> Maybe [(Term,Term)]
join x Nothing = Nothing
join x (Just []) = Just [x]
join (v, c) (Just list) =
  case lookup v list of
    Nothing            -> Just ((v,c):list)
    Just (Variable v2) -> Just list
    Just x             -> if x==c
                          then Just list
                          else Nothing


getbindings :: Atom -> AtomMap -> [[(Term,Term)]]
-- return the possible variable bindings associated a non ground atom
getbindings  (Atom pred args) m =
  let x = Map.lookup (pred, (length args)) m in
    case x of
      Nothing -> [[]]
      Just z  -> (getbindings2 args (Set.toList z))


getbindings2 :: [Term] -> [[Term]] ->  [[(Term,Term)]]
getbindings2 x [] = []
getbindings2 x (y:ys) =
  case (match x y) of
    Nothing -> getbindings2 x ys
    Just z  -> z:(getbindings2 x ys)


getbindingsAtoms :: [Atom] -> AtomMap -> [[(Term,Term)]]
getbindingsAtoms [] m = [[]]
getbindingsAtoms (x:xs) m = join2 (getbindings x m) (getbindingsAtoms xs m)


join2 :: [[(Term,Term)]] -> [[(Term,Term)]] -> [[(Term,Term)]]
-- join2 xs ys = [ z | x <- xs, y <- ys, (merge x y)==(Just z)]
join2 [] ys = []
join2 xs [] = []
join2 xs ys =
  do
    x <- xs
    y <- ys
    case (merge x y) of
      Just z  -> return z
      Nothing -> []


merge :: [(Term,Term)] -> [(Term,Term)] -> Maybe [(Term,Term)]
merge [] ys = Just ys
merge (x:xs) ys =
  case (merge2 x ys) of
    Nothing -> Nothing
    Just z  -> merge xs z


merge2 :: (Term,Term) -> [(Term,Term)] -> Maybe [(Term,Term)]
merge2 (k,v) ys =
  case lookup k ys of
    Nothing -> Just ((k,v):ys)
    Just z  -> if v==z
               then Just ys
               else Nothing


-- --------------------------------------------------------------

class Substitutable s where
  applySubs :: [(Term,Term)] -> s -> s
  is_ground :: s -> Bool

instance Substitutable Term where
  applySubs m (Constant x) = (Constant x)
  applySubs m (Identifier x) = (Identifier x)
  applySubs m (Variable x) =
    case lookup (Variable x) m of
      Just y  -> y
      Nothing -> Variable x

  applySubs m (Addition x y) =
    let xsubs = applySubs m x
        ysubs = applySubs m y
    in
    (Addition xsubs ysubs)

  applySubs m (Subtraction x y) =
    let xsubs = applySubs m x
        ysubs = applySubs m y
    in
    (Subtraction xsubs ysubs)

  applySubs m (Multiplication x y) =
    let xsubs = applySubs m x
        ysubs = applySubs m y
    in
    (Multiplication xsubs ysubs)

  applySubs m (Negation x) = Negation $ applySubs m x 

  is_ground (Constant x) = True
  is_ground (Identifier x) = True
  is_ground _ = False

                
instance Substitutable Atom where
  applySubs m (Atom pred []) = (Atom pred [])
  applySubs m (Atom pred x)  = (Atom pred (map (applySubs m) x))
  
  is_ground (Atom pred args) = and (map is_ground args)
  
instance Substitutable Literal where
  applySubs m (PAtom a) = (PAtom (applySubs m a) )
  applySubs m (NAtom a) = (NAtom (applySubs m a))
  
  is_ground (PAtom a) = is_ground a
  is_ground (NAtom a) = is_ground a

  
instance Substitutable Rule where
  applySubs m (Rule h b) = (Rule (applySubs m h) (map (applySubs m) b) )
  
  is_ground (Rule h b) = is_ground h && and (map is_ground b)


groundRule :: AtomMap ->  Rule -> [Rule]
groundRule am r =
  if (is_ground r)
  then [r]
  else
    let listofsubs = getbindingsAtoms (pbody r) am
        subsapps   = map applySubs listofsubs
    in
    map ($r) subsapps

      
groundProgram:: [Rule] -> [Rule]
groundProgram p =
  let am  = insert_atoms emptyAtomMap (heads_p  p)
      pg1 = nub (concatMap  (groundRule am)  p)
  in
  if pg1==p
  then pg1
  else groundProgram pg1


