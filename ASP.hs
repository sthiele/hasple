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

module ASP (
    Atom, Rule(..), facts, anssets
  ) where
  
import Data.List (sort, nub)
-- use sort to order list nub to remove duplicates from list -- maybe use Sets instead?
 
type Atom = String

data Rule = Rule { h' :: Atom
                 , pb' :: [Atom]
                 , nb' :: [Atom] 
                 }

kopf :: Rule -> Atom    
kopf (Rule h pb nb) = h

pbody :: Rule -> [Atom]    
pbody (Rule h pb nb) = pb

showpbody :: [Atom] -> String
showpbody [] = ""
showpbody (x:[]) = x
showpbody (x:xs) = x ++ ", " ++ (showpbody xs)

nbody :: Rule -> [Atom]    
nbody (Rule {h' = h, pb' = pb, nb' = nb}) = nb

shownbody :: [Atom] -> String
shownbody [] = ""
shownbody (x:[]) = "not " ++ x
shownbody (x:xs) =  "not " ++ x ++ ", "++ (shownbody xs)

instance Show Rule where
  show (Rule h [] []) =  h ++"."  
  show (Rule h pb []) =  h ++ " :- "++showpbody pb++"."
  show (Rule h [] nb) =  h ++ " :- "++shownbody nb++"."
  show (Rule h pb nb) =  h ++ " :- "++(showpbody pb)++", "++(shownbody nb)++"."
  
    
instance Eq Rule where
  (Rule h1 pb1 nb1) == (Rule h2 pb2 nb2) = h1==h2 && pb1==pb2 && nb1==nb2


heads_p :: [Rule] -> [Atom]
-- returns the head of all rules without the contradiction symbol "" (all consistent consequences)
heads_p rules = filter (\i -> i/="" ) (nub (map kopf rules))


subsets :: [a] -> [[a]]
subsets []  = [[]]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)


reducepbody :: [Atom] -> [Atom] -> [Atom]
-- reduces a positive body
reducepbody x y = [a | a <- x, not( a `elem` y)]


reducenbody :: [Atom] -> [Atom] -> [Atom]
-- reduces the negative body
reducenbody x y = [a | a <- x, a `elem` y]


-- satrule :: Rule -> [Atom] -> Bool
-- -- satrule returns true if the rule is satified by the set of atoms
-- satrule (h, pb, nb) x =  if h `elem` x
--       then []==reducepbody pb x && []==reducenbody nb x
--       else True
-- 
-- 
-- satprogram :: [Rule] -> [Atom] -> Bool
-- -- returns true if all rules are satisfied by the set of atoms
-- satprogram [] x = True
-- satprogram p  x = all (\r -> satrule r x) p
-- 
-- -- models p = filter (\i -> satprogram p i) (subsets (heads_p p))


facts :: [Rule] -> [Atom]
-- return the facts of a programm
facts p = [ (kopf r) |  r <- p,  (pbody r)==[], (nbody r)==[] ]


reducebasicprogram :: [Rule] -> [Atom] -> [Rule]
reducebasicprogram p x = [ (Rule (kopf r) (reducepbody (pbody r) x) []) |  r <- p, (pbody r)/=[] ]


cn :: [Rule] -> [Atom]
-- return the consequences of a  basic logic programm
cn [] = []
cn p = if (reducebasicprogram p (facts p))==p 
   then (facts p) 
   else nub ((facts p) ++ (cn (reducebasicprogram p (facts p))))
   
   
reduct :: [Rule] -> [Atom] -> [Rule]
-- return the reduct of a logic program with x
reduct p x = [ (Rule (kopf r) (pbody r) []) |  r <- p,  (reducenbody (nbody r) x)==[] ]

   
anssets p = filter (\i -> (sort (cn (reduct p i)))==(sort i)) (subsets (heads_p p))



p1 = [ (Rule "q" [] []),
       (Rule "p" ["q"] ["r"]) ]

p2 = [ (Rule "q" [] []),
       (Rule "p" ["p"] ["r"]) ]

p3 = [ (Rule "p" [] ["q"]),
       (Rule "q" [] ["p"]) ]

p4 = [ (Rule "p" [] ["p"])]

px = [ (Rule "p" [] ["q","r"]),
       (Rule "q" [] ["p","r"]),
       (Rule "r" [] ["p","q"]),
       (Rule "" ["r"] []),
       (Rule "p" [] ["q","r"])
       ]

data Answer = SAT [[Atom]] | UNSAT [Atom]

instance Show Answer where
  show (SAT x) =  "SAT: " ++ show x
  show (UNSAT x)   =  "UNSAT: " ++ show x

 
sol :: Answer -> [[Atom]]
sol (UNSAT s) = []
sol (SAT s) = s


-- given a list of boolean variables returns all possible interpretations
assignment_generator c = (subsets c)

-- test whether cond is satified by candidate
-- tester for an answer set
test:: [Rule] -> [Atom] -> Bool
test p candidate = (sort (cn (reduct p candidate)))==(sort candidate)


-- choose heuristic
-- use info to reorder the candidates such that the most prefered is first
choose:: [a] -> info -> [a]
-- very stupid heuristic
choose x info = x

findas:: [Rule] -> Int -> Answer
-- return atmost n answer sets for program p
findas p n =
  let variables= (heads_p p)
  in check p (assignment_generator variables) n

check:: [Rule] -> [[Atom]] -> Int ->  Answer
check cond [] num = UNSAT ["f","a","i","l"]
check cond candidates num=
  if ((test cond (head candidates)))
     then  if (num==1)
       then SAT [(head candidates)]
       else
    --    learn answer
       SAT ((head candidates): sol (check cond (tail candidates) (num-1)))
     else
    --    let conflicts=conflictana
       check cond (tail candidates) (num)

