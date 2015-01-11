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

                
                



type MapOfSets =  Map.Map (String, Int) (Set.Set [Term])     

insert_mos:: MapOfSets -> (String, Int) -> [Term] -> MapOfSets      
insert_mos mos key val = 
    case Map.lookup key mos of 
      Nothing -> Map.insert key (Set.insert val Set.empty) mos
      Just x  -> Map.insert key (Set.insert val x) mos

      
--TODO rename to get mos      
getpredval:: [Atom] -> MapOfSets
getpredval [] = Map.empty
getpredval ((Atom pred args):xs) = insert_mos (getpredval xs) (pred, (length args)) args




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
                    



getbindings:: Atom -> MapOfSets -> [[(Term,Term)]]
getbindings  (Atom pred args) m = 
  let x = Map.lookup (pred, (length args)) m in
      case x of
           Nothing -> []
           Just z ->  (getbindings2 args (Set.toList z))

getbindings2:: [Term] -> [[Term]] ->  [[(Term,Term)]]
getbindings2 x [] = []
getbindings2 x (y:ys) = 
  case (match x y) of
       Nothing -> (getbindings2 x ys)
       Just z -> z:(getbindings2 x ys)
       
       
getbindingsAtoms:: [Atom] -> MapOfSets -> [[(Term,Term)]]
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

       
       
       
       
       
arg1 = [ (constant "a"), (constant "a"), (constant "c")]
arg2 = [ (constant "a"), (constant "b"), (constant "e")]
arg3 = [ (constant "b"), (constant "c"), (constant "d")]
arg4 = [ (constant "a"), (constant "c"), (constant "e")]
arg5 = [ (constant "c"), (constant "b"), (constant "a")]

arg6 = [ (constant "a"), (constant "b")]
arg7 = [ (constant "a"), (constant "a")]
arg8 = [ (constant "b"), (constant "c")]
arg9 = [ (constant "a"), (constant "e")]
arg10 = [ (constant "c"), (constant "b")]


arg11 = [ (variable "X"), (constant "b"), (constant "c")]
arg12 = [ (variable "X"), (variable "X"), (constant "c")]
arg13 = [ (variable "X"), (variable "Y"), (constant "e")]


a1 = (Atom "a" arg1)
a2 = (Atom "a" arg2)
a3 = (Atom "a" arg3)
a4 = (Atom "a" arg5)
a5 = (Atom "a" arg6)
a6 = (Atom "a" arg9)
a7 = (Atom "a" arg10)

a8 = (Atom "a" arg12)
a9 = (Atom "a" arg13)

b1 = (Atom "b" arg1)
b2 = (Atom "b" arg2)
b3 = (Atom "b" arg4)
b4 = (Atom "b" arg6)
b5 = (Atom "b" arg7)
b6 = (Atom "b" arg8)
b7 = (Atom "b" arg10)

b8 = (Atom "b" arg11)
b9 = (Atom "b" arg13)


mos1 = getpredval [a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7]       

mySubs1 = getbindings a8 mos1  
mySubs2 = getbindings a9 mos1  
mySubs3 = getbindings b8 mos1  
mySubs4 = getbindings b9 mos1  

mySubsx = getbindingsAtoms [a8,a9,b9] mos1  
mySubsy = getbindingsAtoms [a8,a9,b8,b9] mos1  
