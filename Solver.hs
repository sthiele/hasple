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
   MapOfSets, insert_mos,
   pos_dep_graph,
   scc,
   tarjan,
   
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
   in
   [ a | a <-nfact_candidates, not (hasmatch a he) ]

hasmatch:: Atom -> [Atom] -> Bool
-- returns True if a matching atom exists in the list
hasmatch a [] = False  
hasmatch a (b:bs) =
  case matchAtom a b of
    Just x  -> True
    Nothing -> hasmatch a bs
    
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
       
data Lit = ALit Atom
         | BLit [Atom] [Atom]
         deriving (Show,Eq)
           
type Clause = ([Lit],[Lit])


atoms2lits:: [Atom] -> [Lit]
atoms2lits as = [(ALit a) | a <- as ]

bodies2lits:: [([Atom],[Atom])] -> [Lit]
bodies2lits bs = [(BLit pb nb) | (pb,nb) <- bs ]


bodies_p:: [Rule] -> [([Atom],[Atom])]
-- returns all bodies of a program
bodies_p p = [((pbody r),(nbody r)) | r <-p ]


bodies:: [Rule] -> Atom -> [([Atom],[Atom])]
-- returns all bodies of rules with the atom as head
bodies p a  = [((pbody r),(nbody r)) | r<-p , (kopf r)==a ]


at:: ([Lit],[Lit]) -> [Atom]
-- return the atoms that are true in the assignement
at (ast,asf) = concatMap truelit2trueatoms ast

af:: ([Lit],[Lit]) -> [Atom]
-- return the atoms that are false in the assignement
af (ast,asf) = concatMap falselit2falseatoms asf


truelit2trueatoms (ALit a) = [a]
truelit2trueatoms (BLit pb nb) = pb

falselit2falseatoms (ALit a) = [a]
falselit2falseatoms (BLit pb nb) = []


-- no_good generation ------------------------------

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


get_ng1:: ([Atom],[Atom]) -> Clause
get_ng1 (pb,nb) = ( (atoms2lits nb) , ((BLit pb nb):(atoms2lits pb)) )


get_ng2:: ([Atom],[Atom]) -> [Clause]
get_ng2 (pb,nb) =
  let
    clauses1 = [ ([(BLit pb nb)],[(ALit atom)]) | atom <- pb ]
    clauses2 = [ ([(BLit pb nb),(ALit atom)],[]) | atom <- nb ]
  in
  clauses1 ++ clauses2


get_ng3:: [Rule] -> Atom -> [Clause]
get_ng3 p a = [ ([(BLit pb nb)],[(ALit a)]) | (pb,nb) <- (bodies p a) ]


get_ng4:: [Rule] -> Atom -> Clause
get_ng4 p a = ([(ALit a)], (bodies2lits (bodies p a)))


external_bodies:: [Rule] -> [Atom] -> [([Atom],[Atom])]
-- returns the external bodies
external_bodies p u =
  [ ((pbody r),(nbody r)) |  r <- p, elem (kopf r) u, (intersect (pbody r) u)==[] ]


loop_nogood:: Atom -> [([Atom],[Atom])] -> Clause
-- returns the loop nogood for an atom in an unfounded set(characterized by the external bodies)
loop_nogood a bodies = ([(ALit a)],(bodies2lits bodies))


loop_nogoods:: [Rule] -> [Atom] -> [Clause]
-- return the loop nogoods of the program for a given unfounded set
loop_nogoods p u = [ (loop_nogood atom (external_bodies p u)) | atom<-u  ]


-- ---------------------------------------------------------------------------------
type PosDepGraph = (Map.Map Atom [Atom])

pos_dep_graph:: [Rule] -> PosDepGraph
-- returns the positive dependency graph of a program
pos_dep_graph [] = Map.empty
pos_dep_graph (r:rs) =
  let h = kopf r
      pb = pbody r 
      rg = pos_dep_graph rs
  in
  case Map.lookup h rg of
      Nothing -> Map.insert h pb rg
      Just x  -> Map.insert h (pb++x) rg


scc:: Atom -> PosDepGraph -> [Atom]
-- returns the strongly connected componet of an atom
scc a depg = tarjan depg [] [] a

tarjan:: PosDepGraph -> [Atom] -> [Atom] -> Atom -> [Atom]
tarjan depg visited visited2 a =
   if (elem a visited)
   then 
     case Map.lookup a depg of
       Nothing -> []
       Just x  -> let next = x \\ visited2 in
                  (a:(concatMap (tarjan depg visited (a:visited2)) next))
   else
     case Map.lookup a depg of
       Nothing -> []
       Just x  -> let next = x \\ visited2 in
                  (concatMap (tarjan depg (a:visited) visited2) next)



cyclic:: Atom -> [Rule] -> Bool
cyclic a p =
  let scc_a = scc a (pos_dep_graph p)
  in
  check_scc scc_a p

check_scc:: [Atom] -> [Rule] -> Bool
-- returns True if there is a rule with head in scc and body+ with not empty
check_scc sc [] = False
check_scc sc (r:rs) =
 ( (elem (kopf r) sc) && ((intersect (pbody r) sc) /= [])) || (check_scc sc rs)


unfounded_set:: [Rule] -> ([Lit],[Lit]) -> [Atom]
-- returns an unfounded set for the program given a partial assignment
unfounded_set p assig =
  let s = collect_nonfalse_cyclic_atoms assig p
      s2 = extend p assig emptysourcep s
      -- bis line 5
  in
  []


collect_nonfalse_cyclic_atoms:: ([Lit],[Lit]) -> [Rule] -> [Atom]
collect_nonfalse_cyclic_atoms (ast,asf) p =
  let atoms = (atoms_p p)
  in
  [ a | a<- atoms , not (cyclic a p)]
      

extend:: [Rule] -> ([Lit],[Lit]) -> SourcePointerConf -> [Atom]  -> [Atom]
extend p assig spc s =
  let
    helper1 =  (af assig)++s
    atoms = (atoms_p p)
    helper2 = atoms \\ helper1
    t =[ a | a <- helper2, (intersect (sourcep a spc) (intersect (scc a (pos_dep_graph p)) s)) /= [] ]
  in
    if t==[]
    then s++t
    else extend p assig spc (s++t) 
  

type SourcePointerConf =   (Map.Map Atom Lit)
emptysourcep:: SourcePointerConf
emptysourcep = Map.empty


bottom = (ALit __conflict)

source:: Atom -> SourcePointerConf -> Lit
source a spc =
   case Map.lookup a spc of
       Nothing -> bottom
       Just x  ->  x

sourcep:: Atom -> SourcePointerConf -> [Atom]
sourcep a spc =
  let (BLit pb nb)= (source a spc)
  in
  pb
      







local_propagation:: [Rule] -> [Clause] -> ([Lit],[Lit]) -> Maybe ([Lit],[Lit])
-- takes a program a set of nogoods and an assignment and returns a new assignment
local_propagation p ngs assig =
  let ngs_p = (nogoods_of_lp p) ++ ngs
      up = unitpropagate assig ngs_p
  in
    case up of
      Just newassig -> if newassig == assig
                       then Just assig
                       else local_propagation [] ngs_p newassig
      Nothing       -> Nothing -- return conflict clause


  

unitpropagate:: ([Lit],[Lit]) -> [Clause] -> Maybe ([Lit],[Lit])
unitpropagate (at, af) [] = Just (at, af)
unitpropagate (at, af) (ng:ngs) =
  let x = unitresult (at,af) ng in
  case x of
       Just ([nt],[]) -> unitpropagate ((nt:at),af) ngs
       Just ([],[nf]) -> unitpropagate (at,(nf:af)) ngs
       Nothing        -> Nothing -- return conflict clauses
       
       
  
unitresult:: ([Lit],[Lit]) -> Clause -> Maybe ([Lit],[Lit])
-- An assignement a nogood  maybe a new assignment or a conflict
unitresult (at, af) (ngt, ngf) =
  case (ngt \\ at) of
    []      -> case (ngf \\ af) of
                 []      -> Nothing -- return conflict clauses1
                 [sigma] -> Just ([sigma],[])
                 _       -> Just ([],[]) -- nothing can be derived
         
    [sigma] -> case (ngf \\ af) of
                 []      -> Just ([],[sigma])
                 _       -> Just ([],[]) -- nothing can be derived
    
    _ -> Just ([],[]) -- nothing can be derived


is_solution:: ([Lit],[Lit]) -> [Clause] -> Bool
-- An assignment violates a set nogoods if one nogood is contained in the assignment
is_solution a (ng:ngs) =  (is_sol a ng) && (is_solution a ngs)

is_sol:: ([Lit],[Lit]) -> Clause -> Bool
-- An assignment violates a nogoods if the nogood is contained in the assignment
is_sol (at,af) (ngt,ngf) =   (intersect ngt at)/=ngt || (intersect ngf af)/=ngf




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
