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

module Solver (
   anssets,
   reduct, cn,
   groundProgram, groundProgramx,
   consequences, simplifyProgramm,
     simplifyProgramm2,
       heads_p, atoms_p,
   get_query_rules, getpredval, getpredvalx, groundRule, get_ics,
   MapOfSets, insert_mos  
  ) where

import ASP
import Data.List (sort, nub, intersect, (\\), delete )
import Data.Maybe -- for mapMaybe
-- import Data.List.Extra (nubOrd)
-- use sort to order list nub (nubOrd) to remove duplicates from list -- maybe use Sets instead?
import qualified Data.Set as Set
import qualified Data.Map as Map


-- type MapOfSets =  Map.Map (String, Int) (Set.Set Atom)
type MapOfSets =  Map.Map (String, Int) (Set.Set [Term])     

-- insert_mos:: MapOfSets -> Atom -> MapOfSets
insert_mos:: MapOfSets -> (String, Int) -> [Term] -> MapOfSets      
-- insert_mos mos key val = 
--     case Map.lookup key mos of 
--       Nothing -> if (allconst val)
--                     then Map.insert key (Set.insert val Set.empty) mos
--                     else mos
--       Just x  -> if (allconst val)
--                     then Map.insert key (Set.insert val x) mos
--                     else mos
                    
insert_mos mos key val = 
    case Map.lookup key mos of 
      Nothing -> Map.insert key (Set.insert val Set.empty) mos                 
      Just x  -> Map.insert key (Set.insert val x) mos
                 
                    
                    

-- allconst:: [Term] -> Bool
-- allconst [] = True
-- allconst ((Identifier x):xs) = True && allconst xs
-- allconst ((Constant x):xs) = True && allconst xs
-- allconst _ = False


      
--TODO rename to get mos      
getpredval:: [Atom] -> MapOfSets
getpredval [] = Map.empty
getpredval ((Atom pred args):xs) = insert_mos (getpredval xs) (pred, (length args)) args


getpredvalx:: MapOfSets -> [Atom] -> MapOfSets
getpredvalx mos [] = mos
getpredvalx mos ((Atom pred args):xs) =
  let mos2 = insert_mos mos (pred, (length args)) args
  in
    getpredvalx mos2 xs


-- can two terms be unified if yes return variable bindings
matchTerm:: Term -> Term -> Maybe [(Term,Term)]
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



                      

-- can two argumentlist be unified if yes return variable bindings
match:: [Term] -> [Term] -> Maybe [(Term,Term)]
match [] [] = Just []
match (x:xs) (y:ys) = 
  if (length xs) == (length ys) 
     then 
     case (matchTerm x y) of
          Nothing -> Nothing
          Just [] ->  (match xs ys)     
          Just [(var,const)] -> join (var,const) (match xs ys)
     else Nothing
     
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



-- return the possible variable bindings associated a non ground atom
getbindings:: Atom -> MapOfSets -> [[(Term,Term)]]
getbindings  (Atom pred args) m = 
  let x = Map.lookup (pred, (length args)) m in
      case x of
           Nothing -> [[]]
           Just z ->  (getbindings2 args (Set.toList z))

-- getbindings2:: [Term] -> [Atom] ->  [[(Term,Term)]]
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

   
-- --------------------------------------------------------------

subsTerm:: [(Term,Term)] -> Term -> Term
-- subsTerm:: Map.Map Term Term -> Term -> Term
subsTerm m (Constant x) = (Constant x)
subsTerm m (Identifier x) = (Identifier x)
subsTerm m (Variable x) =
              case lookup (Variable x) m of
                Just y -> y
                Nothing -> (Variable x)
                
subsTerm m (Addition x y) =
              let xsubs = subsTerm m x
                  ysubs = subsTerm m y
              in (Addition xsubs ysubs)

subsTerm m (Subtraction x y) =
              let xsubs = subsTerm m x
                  ysubs = subsTerm m y
              in (Subtraction xsubs ysubs)
              
subsTerm m (Multiplication x y) =
              let xsubs = subsTerm m x
                  ysubs = subsTerm m y
              in (Multiplication xsubs ysubs)
              
subsTerm m (Negation x) =
              let xsubs = subsTerm m x
              in (Negation xsubs)
              
              

subsAtom:: [(Term,Term)] -> Atom -> Atom
-- subsAtom:: Map.Map Term Term -> Atom -> Atom
subsAtom m (Atom pred []) = (Atom pred [])
subsAtom m (Atom pred x)  = (Atom pred (map (subsTerm m) x))

groundRule2:: Rule -> [(Term,Term)] -> Rule
groundRule2 (Rule h pb nb) m= (Rule (subsAtom m h) (map (subsAtom m) pb) (map (subsAtom m) nb))

-- ground_rules2:: [[(Term,Term)]] ->  Rule -> [Rule]
-- ground_rules2 xs r = map (ground_rule r) xs

-- alternative
groundRule:: MapOfSets ->  Rule -> [Rule]
groundRule m (Rule h pb nb) =
  if (is_groundRule (Rule h pb nb))
  then [(Rule h pb nb)]
  else
    let c =  getbindingsAtoms pb m
    in  nub (map (groundRule2 (Rule h pb nb)) c)


groundProgram:: [Rule] -> [Rule]
groundProgram p =
  let m = getpredval (heads_p  p)
      pg1 = nub (concatMap  (groundRule m)  p)
  in
    if pg1==p
       then pg1
       else groundProgram pg1
      
groundProgramx:: [Rule] -> MapOfSets -> [Rule]
groundProgramx p mos =
  let m = getpredvalx mos (heads_p  p)
      pg1 = nub (concatMap  (groundRule m)  p)
  in
    if pg1==p
       then pg1
       else groundProgram pg1

      

-- --------------------------------------------------------------


heads_p :: [Rule] -> [Atom]
-- returns the head of all rules without the contradiction symbol "" (all consistent consequences)
heads_p rules =
  filter (\i -> i/=__conflict )
  (nub (map kopf rules))

atoms_p :: [Rule] -> [Atom]
atoms_p rules =
  filter (\i -> i/=__conflict )
  (nub (map kopf rules)++ (concatMap pbody rules) ++ (concatMap pbody rules))

subsets :: [a] -> [[a]]
subsets []  = [[]]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)


-- \\ in reducebasicprogram
-- reducepbody :: [Atom] -> [Atom] -> [Atom]
-- -- reduces a positive body
-- reducepbody x y = [a | a <- x, not( a `elem` y)]

-- intersect in reducebasicprogram
-- reducenbody :: [Atom] -> [Atom] -> [Atom]
-- -- reduces the negative body
-- reducenbody x y = [a | a <- x, a `elem` y]


facts :: [Rule] -> [Atom]
-- return the facts of a programm
facts p = [ (kopf r) |  r <- p,  (null (pbody r)), (null (nbody r)) ]


reducebasicprogram :: [Rule] -> [Atom] -> [Rule]
reducebasicprogram p x = [ (Rule (kopf r) ((pbody r)\\ x) []) | r <- p, (pbody r)/=[] ]


cn :: [Rule] -> [Atom]
-- return the consequences of a  basic logic programm
cn [] = []
cn p = if (reducebasicprogram p (facts p)) == p
   then (facts p)
   else nub ((facts p) ++ (cn (reducebasicprogram p (facts p))))

   
reduct :: [Rule] -> [Atom] -> [Rule]
-- return the reduct of a logic program with x
reduct p x = [ (Rule (kopf r) (pbody r) []) |  r <- p,  (intersect (nbody r) x)==[] ]


anssets p = filter (\i -> (sort (cn (reduct p i)))==(sort i)) (subsets (heads_p p))







-- returns the integrity constraints of a program  
get_ics:: [Rule] -> [Rule]
get_ics [] = []
get_ics ((Rule h pb nb):rs) =
  if (h == __conflict)
  then ((Rule h pb nb): get_ics rs)
  else get_ics rs

-- return true if a rule does not contain variables
is_groundRule:: Rule -> Bool
is_groundRule (Rule h pb nb) = is_groundAtom h && is_groundAtoms pb && is_groundAtoms nb

-- returns true if the list of Atoms does not contain variables
is_groundAtoms:: [Atom] -> Bool
is_groundAtoms [] = True
is_groundAtoms (x:xs) = is_groundAtom x && is_groundAtoms xs

-- returns true if the atom does not contain variables
is_groundAtom:: Atom -> Bool
is_groundAtom (Atom pred args) = is_groundTerms args

-- returns true if the list of Terms only consists of constants
is_groundTerms:: [Term] -> Bool
is_groundTerms [] = True
is_groundTerms ((Constant x):xs) = is_groundTerms xs
is_groundTerms ((Identifier x):xs) = is_groundTerms xs
is_groundTerms _ = False

-- does remove facts
simplifyProgramm:: [Rule] -> ([Atom],[Atom]) -> [Rule]
simplifyProgramm [] (t,f) = []
simplifyProgramm x (t,f) = (mapMaybe (simplifyRule (t,f)) x)

-- does not remove facts
simplifyProgramm2:: [Rule] -> ([Atom],[Atom]) -> [Rule]
simplifyProgramm2 [] (t,f) = []
simplifyProgramm2 x (t,f) = (mapMaybe (simplifyRule2 (t,f)) x)


simplifyRule:: ([Atom],[Atom]) -> Rule -> Maybe Rule
simplifyRule (t,f) (Rule h pb nb) =
  if ( (elem h t) || not (null (intersect nb t)) || not (null (intersect pb f)))
  then Nothing
  else
  let newpbody = (nub pb) \\ t
      newnbody = (nub nb) \\ f
  in
  Just (Rule h newpbody newnbody)
  
-- does not remove facts
simplifyRule2:: ([Atom],[Atom]) -> Rule -> Maybe Rule
simplifyRule2 (t,f) (Rule h pb nb) =
  if ( not (null (intersect nb t)) || not (null (intersect pb f)))
  then Nothing
  else
  let newpbody = (nub pb) \\ t
      newnbody = (nub nb) \\ f
  in
  Just (Rule h newpbody newnbody)  
         
-- return consequences of a programm
-- consequences :: [Rule] -> [Atom] -> [Atom] -> ([Atom],[Atom])
-- consequences p t f=
--   let
--       simplified_prg = simplifyProgramm2 p (t,f)
--       trues = facts simplified_prg
--       falses  = nfacts simplified_prg
--   in
--   if (null (trues \\ t) && null (falses \\ f))
--   then (t,f)
--   else
--     let t2 = t ++ trues
--         f2 = f ++ falses
--     in
--       consequences simplified_prg t2 f2

consequences :: [Rule] -> [Atom] -> [Atom] -> ([Atom],[Atom])
consequences p t f=
  let reduced = reduct p t
      simplified_prg = simplifyProgramm2 p (t,f)
      trues = facts simplified_prg
      falses  = nfacts simplified_prg
  in
  if (null (trues \\ t) && null (falses \\ f))
  then (t,f)
  else
    let t2 = t ++ trues
        f2 = f ++ falses
    in
      consequences simplified_prg t2 f2
      
-- return atoms of a programm that dont have a matching head
nfacts :: [Rule] -> [Atom]
nfacts prg =
   let a = nub (atoms_p prg)
       he = heads_p prg
       nfact_candidates = (a \\ he)
       discard = concatMap (testy he) nfact_candidates
   in
     nfact_candidates \\ discard
     
testy:: [Atom] -> Atom -> [Atom]
testy [] a = []
testy (x:xs) a =
  case matchAtom a x of
     Just x -> [a]
     Nothing -> testy xs a
     

get_query_rules:: [Rule] -> Atom -> [Rule]
get_query_rules [] _ = []
get_query_rules rules a =
  let grules = get_query_rules2 rules a
      next = (concatMap pbody grules) ++ (concatMap nbody grules)
      nn = delete a next
  in
    nub (grules ++ (concatMap (get_query_rulesx rules [a]) nn))

get_query_rulesx:: [Rule] -> [Atom] -> Atom -> [Rule]
get_query_rulesx rules found a =
  let grules = get_query_rules2 rules a
      next = (concatMap pbody grules) ++ (concatMap nbody grules)
      nn = next \\ (a:found)
  in
    grules ++ (concatMap (get_query_rulesx rules (a:found)) nn)



get_query_rules2:: [Rule] -> Atom -> [Rule]
get_query_rules2 [] _ = []
get_query_rules2 (r:rs) a = 
  case matchAtom (kopf r) a of
       Just binding ->  let gr = groundRule2 r binding
                            grs = get_query_rules2 rs a
                        in
                        nub (gr: grs)
       Nothing -> get_query_rules2 rs a


-- ------------------------------------------------------------
       
data Stuff = Lit Atom
           | Body [Atom] [Atom]
           deriving (Show)


mogrify:: [Atom] -> [Stuff]
mogrify [] = []
mogrify (a:as) = ((Lit a):mogrify as)

-- returns all bodies of a program
bodies_p:: [Rule] -> [([Atom],[Atom])]
bodies_p [] = []
bodies_p (r:rs) = (((pbody r),(nbody r)):(bodies_p rs))

-- returns all bodies of rules with the atom as head
bodies:: [Rule] -> Atom -> [([Atom],[Atom])]
bodies [] a = []
bodies (r:rs) a  = 
  if (kopf r)==a
  then (((pbody r),(nbody r)):(bodies rs a))
  else (bodies rs a)

type Clause = ([Stuff],[Stuff])


nogoods_of_lp:: [Rule] -> [Clause]
nogoods_of_lp p =
  let a = atoms_p p
      b = bodies_p p
      ng1 = map get_ng1 b
      ng2 = concatMap get_ng2 b
      ng3 = concatMap (get_ng3 p) a
      ng4 = map (get_ng4 p) a
  in
  ng1++ng2++ng3++ng4


get_ng4:: [Rule] -> Atom -> Clause
get_ng4 p a =
  let b = bodies p a in
  ([(Lit a)], (murkel b))    

-- Bodies 2 Stuff
murkel:: [([Atom],[Atom])] -> [Stuff]
murkel [] = []
murkel ((pb,nb):bs) = ((Body pb nb):(murkel bs))

get_ng3:: [Rule] -> Atom -> [Clause]
get_ng3 p a =
  let b = bodies p a
  in
  map (melt (Lit a)) (murkel b)

melt:: Stuff -> Stuff -> Clause
melt atom body = ([body],[atom])

get_ng1:: ([Atom],[Atom]) -> Clause  
get_ng1 (pb,nb) = ( (mogrify nb) , ((Body pb nb):(mogrify pb)) )

get_ng2:: ([Atom],[Atom]) -> [Clause]
get_ng2 (pb,nb) =
  let p_clauses = map ( makepair1 (Body pb nb)) (mogrify pb)
      n_clauses = map ( makepair2 (Body pb nb)) (mogrify nb)
  in
  p_clauses ++ n_clauses

makepair1 body atom = ([body],[atom])
makepair2 body atom = ([body,atom],[])

 


ac = (Atom "a" [(Identifier "c")])
av = (Atom "a" [(Variable "X")])

bv = (Atom "b" [(Variable "X")])
bc = (Atom "b" [(Constant 1 )])


rv = (Atom "r" [(Variable "X")])
rc = (Atom "r" [(Identifier "x")])

mp = [
        (Rule ac [] []),
        (Rule bv [av] [])
      ]

x1 = (Atom "a" [(Variable "X"),(Variable "X")])
t1 = [(Variable "X"),(Variable "X")]
x2 = (Atom "a" [(Variable "Y"),(Variable "Z")])
t2 = [(Variable "Y"),(Variable "Z")]
x3 = (Atom "a" [(Constant 1),(Constant 1)])
t3 = [(Identifier "a"),(Identifier "a")]
x4 = (Atom "a" [(Identifier "a"),(Identifier "b")])
t4 = [(Identifier "a"),(Identifier "b")]
