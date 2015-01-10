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
    Atom, Rule(..)
  ) where
  
import Data.List (sort, nub)
-- use sort to order list nub to remove duplicates from list -- maybe use Sets instead?
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
 
--my showlist 
showlist :: (Show a) => [a] -> String
showlist [] = ""
showlist (x:[]) = (show x)
showlist (x:xs) = (show x)  ++ "," ++ (showlist xs)

  
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
  
    
-- instance Eq Rule where
--   (Rule h1 pb1 nb1) == (Rule h2 pb2 nb2) = h1==h2 && pb1==pb2 && nb1==nb2



data Atom = Atom { predicate :: String
                 , arguments :: [Term]
                 }
-- instance Ord Atom where
--   compare (Atom pred args) (Atom pred2 args2) = compare pred pred2
instance Show Atom where
    show (Atom pred []) =  pred
    show (Atom pred xs) =  pred ++"("++showlist xs++")"
-- instance Eq Atom where
--   (Atom p1 args1) == (Atom p2 args2) = p1==p2 && args1==args2


        
data Term = Term { is_const :: Bool
                 , name :: String
                 }
-- Konst :: String -> Term
constant x = (Term True x)

-- Variable :: String -> Term
variable x = (Term False x)

instance Show Term where
  show (Term True x) =  show x
  show (Term False x) = x
    
instance Ord Term where
  compare (Term True args) (Term False args2) = compare True  False
  compare (Term False args) (Term True args2) = compare False True
  compare (Term True args) (Term True args2) = compare args args2
  compare (Term False args) (Term False args2) = compare args args2
instance Eq Term where
  (Term b1 args1) == (Term b2 args2) = b1==b2 && args1==args2



    
     
-- instance Eq Term where
--   (Konst x) == (Konst x2) = x==x2
--   (Variable x) == (Variable x2) = x==x2
--   

subsTerm:: Map.Map Term Term -> Term -> Term
subsTerm m (Term True x) = (Term True x)
subsTerm m x =
              case Map.lookup x m of
                Just y -> y
                Nothing -> x

subsAtom:: Map.Map Term Term -> Atom -> Atom
subsAtom m (Atom pred []) = (Atom pred [])
subsAtom m (Atom pred x)  = (Atom pred (map (subsTerm m) x))

                
                
-- define a substitution                
mySub = Map.insert (variable "X") (constant "const") Map.empty
test = (Atom "a" [(variable "X"),(variable "Y")])


a1 = (Atom "a" [(constant "a")])
a2 = (Atom "a" [(variable "X")])
b  = (Atom "b" [(variable "X")])

p6 = [ (Rule a1 [] []),
       (Rule b [a2] []) ]



type MapOfSets =  Map.Map (String, Int) (Set.Set [Term])     

insert_mos:: MapOfSets -> (String, Int) -> [Term] -> MapOfSets      
insert_mos mos key val = 
    case Map.lookup key mos of 
      Nothing -> Map.insert key (Set.insert val Set.empty) mos
      Just x  -> Map.insert key (Set.insert val x) mos

getpredval:: [Atom] -> MapOfSets
getpredval [] = Map.empty
getpredval ((Atom pred args):xs) = insert_mos (getpredval xs) (pred, (length args)) args

{-
getbindings:: Atom -> MapOfSets -> Map.Map Term Term
getbindings  (Atom pred args) m = 
  let x = Map.lookup (preds, (length args)) in
  matching args x

matching:: [Term] -> [[Term]] -> [[Term]]
-}


matchTerm:: Term -> Term -> Maybe [(Term,Term)]
matchTerm (Term True x) (Term True y) = 
  if x==y 
     then Just []
     else Nothing
matchTerm (Term False x) (Term True y) = Just [ ((Term False x),(Term True y))]
matchTerm (Term False x) (Term False y) = Just []
matchTerm (Term True x) (Term False y) = Nothing


match:: [Term] -> [Term] -> Maybe [(Term,Term)]
match [] [] = Just []
match (x:xs) (y:ys) = 
  if (length xs) == (length ys) 
     then 
     case (matchTerm x y) of
          Nothing -> Nothing
          Just [] ->  (match xs ys)     
          Just [((Term False x),(Term True y))] -> join ((Term False x),(Term True y)) (match xs ys)
     else Nothing

join:: (Term,Term) -> Maybe [(Term,Term)] -> Maybe [(Term,Term)]
join x Nothing = Nothing
join x (Just []) = Just [x]
join (v, c) (Just list) = 
      case lookup v list of
           Nothing -> (Just ((v,c):list))
           Just x -> if x==c 
                        then Just list
                        else Nothing
                    


arg1 = [ (constant "a"), (constant "b"), (constant "c")]
arg2 = [ (variable "X"), (constant "b"), (constant "c")]
arg3 = [ (variable "X"), (variable "X"), (constant "c")]



