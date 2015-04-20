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
   reduct,
   facts,
   cdnl_enum,
  ) where
    
import Debug.Trace
import ASP
import Types
import Data.List (sort, nub, intersect, (\\), delete )
import Data.Maybe 
-- import Data.List.Extra (nubOrd)
-- use sort to order list nub (nubOrd) to remove duplicates from list -- maybe use Sets instead?
import qualified Data.Map as Map


-- --------------------------------------------------------------


subsets:: [a] -> [[a]]
subsets []  = [[]]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)


facts:: [Rule] -> [Atom]
-- return the facts of a programm
facts p = [ (kopf r) |  r <- p,  (null (pbody r)), (null (nbody r)) ]


reducebasicprogram:: [Rule] -> [Atom] -> [Rule]
reducebasicprogram p x = [ (basicRule (kopf r) ((pbody r)\\ x) ) | r <- p, (pbody r)/=[] ]


cn:: [Rule] -> [Atom]
-- return the consequences of a  basic logic programm
cn [] = []

cn p = if (reducebasicprogram p (facts p)) == p
   then (facts p)
   else nub ((facts p) ++ (cn (reducebasicprogram p (facts p))))


reduct:: [Rule] -> [Atom] -> [Rule]
-- return the reduct of a logic program with x
reduct p x = [ (basicRule (kopf r) (pbody r)) |  r <- p,  (intersect (nbody r) x)==[] ]


anssets:: [Rule] -> [[Atom]]
anssets p = filter (\i -> (sort (cn (reduct p i)))==(sort i)) (subsets (heads_p p))


-- --------------------------------------------------------------------------------


data SPVar = ALit Atom                                                          -- Solver-Variable
         | BLit [Literal]
         deriving (Show,Eq,Ord)         

__bottom:: SPVar
-- returns the of Solver-variable representing a conflict
__bottom = (ALit __conflict)


atoms2vars:: [Atom] -> [SPVar]
-- returns a list of Solver-variables
atoms2vars as = [(ALit a) | a <- as ]


bodies2vars:: [[Literal]] -> [SPVar]
-- returns a list of Solver-variables
bodies2vars bs = [(BLit b) | b <- bs ]


bodies_p:: [Rule] -> [[Literal]]
-- returns all bodies of a program
bodies_p p = [(body r) | r <-p ]


bodies:: [Rule] -> Atom -> [[Literal]]
-- returns all bodies of rules with the atom as head
bodies p a  = [(body r) | r<-p , (kopf r)==a ]


get_vars:: [CClause] -> [SPVar]
get_vars [] = []
get_vars (c:cs) = nub ((get_varsc c) ++ (get_vars cs))

get_varsc:: CClause -> [SPVar]
get_varsc (t,f) = nub (t ++ f)


falselits:: Assignment -> [SPVar] -> [SPVar]
-- falselits (_,f) = f
falselits x spvars = falselits2 x spvars 1
falselits2 [] spvars n = []
falselits2 ((-1):as) spvars n = ((get_lit n spvars):(falselits2 as spvars (n+1)))
falselits2 (_:as) spvars n = (falselits2 as spvars (n+1))


trueatoms:: Assignment -> [SPVar] -> [Atom]
trueatoms x spvar = trueatoms2 x spvar 1
trueatoms2:: Assignment -> [SPVar] -> Int -> [Atom]
trueatoms2 [] spvar n = []
trueatoms2 (1:as) spvar n = (atomsfromvar (get_lit n spvar))++ (trueatoms2 as spvar (n+1))
trueatoms2 (_:as) spvar n = (trueatoms2 as spvar (n+1))


get_lit:: Int -> [SPVar] -> SPVar
get_lit 1 spvars = head spvars
get_lit n (v:vs) = get_lit (n-1) vs

get_svar:: SPVar -> [SPVar] -> SVar
get_svar l x = get_svar2 l x 1
get_svar2 s (f:ls) n = 
  if s==f
  then n
  else get_svar2 s ls (n+1) 


falseatoms:: Assignment -> [SPVar] -> [Atom]
falseatoms x spvar = falseatoms2 x spvar 1
falseatoms2:: Assignment -> [SPVar] -> Int -> [Atom]
falseatoms2 [] spvar n = []
falseatoms2 ((-1):as) spvar n = (atomsfromvar (get_lit n spvar))++ (falseatoms2 as spvar (n+1))
falseatoms2 (_:as) spvar n = (falseatoms2 as spvar (n+1))


atomsfromvar:: SPVar -> [Atom]
atomsfromvar (ALit a) = [a]
atomsfromvar (BLit b) = [ a | PAtom a <- b]

-- ---------------------------------------------------------------------------------
-- no_good generation


type CClause = ([SPVar],[SPVar])
nogoods_of_lp:: [Rule] -> [CClause]
nogoods_of_lp p =
  let a = (atoms_p p)++[__conflict]
      b = bodies_p p
      ng1 = map get_ng1 b           -- body is true if all lits of it are true -- not ( body=false and all lits=true)
      ng2 = concatMap get_ng2 b     -- body is true if all lits of it are true -- not ( body=true and one lit=false)
      ng3 = concatMap (get_ng3 p) a -- a head is true if one body is true -- not ( head=false and one body=true)
      ng4 = map (get_ng4 p) a       -- a head is true if one body is true -- not ( head=true and all bodies=false=
      ngx = [([__bottom],[])]       -- no conflict literal
  in
  ng1++ng2++ng3++ng4++ngx


get_ng1:: [Literal] -> CClause
get_ng1 b =
  let pb = [ a | PAtom a <- b ]
      nb = [ a | NAtom a <- b ]
  in
  ((atoms2vars pb), ((BLit b):(atoms2vars nb)))


get_ng2:: [Literal] -> [CClause]
get_ng2 b =
  let
    pb = [ a | PAtom a <- b ]
    nb = [ a | NAtom a <- b ]
    clauses1 = [ ([(BLit b)], [(ALit atom)]) | atom <- pb ]
    clauses2 = [ ([(BLit b),(ALit atom)],[]) | atom <- nb ]
  in
  clauses1 ++ clauses2


get_ng3:: [Rule] -> Atom -> [CClause]
get_ng3 p a = [ ([(BLit b)], [(ALit a)]) | b <- (bodies p a) ]


get_ng4:: [Rule] -> Atom -> CClause
get_ng4 p a = ([(ALit a)], (bodies2vars (bodies p a)))


external_bodies:: [Rule] -> [Atom] -> [[Literal]]
-- returns the external bodies
external_bodies p u =
  [ (body r) |  r <- p, elem (kopf r) u, (intersect (pbody r) u)==[] ]


loop_nogood:: Atom -> [[Literal]] -> CClause
-- returns the loop nogood for an atom in an unfounded set(characterized by the external bodies)
loop_nogood a bodies = ([(ALit a)], (bodies2vars bodies))


loop_nogoods:: [Rule] -> [Atom] -> [CClause]
-- return the loop nogoods of the program for a given unfounded set
loop_nogoods p u = [ (loop_nogood atom (external_bodies p u)) | atom<-u  ]



transforms:: [CClause] -> [SPVar] -> [Clause]
transforms [] spvars = []
transforms (c:cs) spvars = ((transform c spvars):(transforms cs spvars))


transform:: CClause -> [SPVar] -> Clause
transform (t,f) spvars = ((transf2 t spvars), (transf2 f spvars))

transf2:: [SPVar] -> [SPVar] -> [SVar]
transf2 [] _ = []
transf2 (spv:spvs) l = ((transf3 spv l): (transf2 spvs l))

transf3:: SPVar -> [SPVar] -> SVar
transf3 spv vars = transf4 spv vars 1
 
transf4:: SPVar -> [SPVar] -> Int -> SVar
transf4 spv (v:vs) n = 
  if spv==v
     then n
     else transf4 spv vs (n+1)


-- ---------------------------------------------------------------------------------
-- unfounded set checker


type PDG = (Map.Map Atom [Atom])                                               -- PositiveDependencyGraph

pos_dep_graph:: [Rule] -> PDG
pos_dep_graph prg = pos_dep_graph2 prg Map.empty

pos_dep_graph2 [] accu = accu

pos_dep_graph2 (r:rs) accu =
  let h = kopf r
      pb = pbody r
  in
  case Map.lookup h accu of
      Nothing -> let naccu = Map.insert h pb accu in
                 pos_dep_graph2 rs naccu
      Just x  -> let naccu = Map.insert h (pb++x) accu in
                 pos_dep_graph2 rs naccu

                 
scc:: Atom -> PDG -> [Atom]
-- returns the strongly connected component of an atom
scc a depg = tarjan depg [] [] a


tarjan:: PDG -> [Atom] -> [Atom] -> Atom -> [Atom]
tarjan depg visited visited2 a  =
   if (elem a visited)
   then
     case Map.lookup a depg of
       Nothing -> (a:visited2)
       Just x  -> let next = x \\ visited2 in
                  if next==[]
                  then (a:visited2)
                  else concatMap (tarjan depg visited (a:visited2)) next
   else
     case Map.lookup a depg of
       Nothing -> visited2
       Just x  -> let next = x \\ visited2 in
                  if next==[]
                  then visited2
                  else concatMap (tarjan depg (a:visited) visited2) next



type SPC =   (Map.Map Atom SPVar)                                               -- SourcePointerC
emptyspc:: SPC
emptyspc = Map.empty


add_source::  SPC -> Atom -> SPVar -> SPC
-- add a new sourcep for an atom
add_source spc a l =  Map.insert a l spc

source:: Atom -> SPC -> SPVar
source a spc =
   case Map.lookup a spc of
       Nothing -> __bottom
       Just x  ->  x

sourcep:: Atom -> SPC -> [Atom]
sourcep a spc =
  case (source a spc) of
  (BLit b) ->  [ a | PAtom a <- b ]
  __bottom -> []  


cyclic:: Atom -> [Rule] -> Bool
-- test if an atom has a cyclic definition might be easier, if scc\=[]
cyclic a p =
  let scc_a = scc a (pos_dep_graph p) in
  not (scc_a == [])


unfounded_set:: [Rule] -> SPC -> Assignment -> [SPVar] -> [Atom]
-- returns an unfounded set for the program given a partial assignment
unfounded_set prg spc assig spvars=
  let s = collect_nonfalse_cyclic_atoms assig spvars prg
      s2 = extend prg assig spvars spc s                                              -- bis line 5
  in
  loop_s 0 prg spc assig spvars s2


collect_nonfalse_cyclic_atoms:: Assignment -> [SPVar] -> [Rule] -> [Atom]
collect_nonfalse_cyclic_atoms assig spvars p =
  let atoms = nub (atoms_p p) \\ (falseatoms assig spvars)
  in
  [ a | a <- atoms, (cyclic a p)]


extend:: [Rule] -> Assignment -> [SPVar] -> SPC -> [Atom]  -> [Atom]
extend p assig spvars spc s =
  let
    helper1 =  (falseatoms assig spvars)++s
    atoms = (atoms_p p)
    helper2 = atoms \\ helper1
    t =[ a | a <- helper2, (intersect (sourcep a spc) (intersect (scc a (pos_dep_graph p)) s)) /= [] ]
  in
    if t==[]
    then s++t
    else extend p assig spvars spc (s++t)


loop_s:: Int -> [Rule] -> SPC -> Assignment -> [SPVar] ->[Atom] -> [Atom]
loop_s num prg spc assig spvars [] = []                                               -- no unfounded_set
loop_s num prg spc assig spvars s =
  let u = head s
      eb = bodies2vars (external_bodies prg [u])
      (spc2,s2,u2,found) = loop_u 0 num prg spc assig spvars s [u] u
  in
  if found
  then u2
  else
    loop_s 1 prg spc2 assig spvars s2


loop_u:: Int-> Int -> [Rule] -> SPC -> Assignment -> [SPVar] -> [Atom] -> [Atom] -> Atom -> (SPC, [Atom], [Atom], Bool)
loop_u num nums prg spc assig spvars s [] p  = (spc, s, [], False)
loop_u num nums prg spc assig spvars s u p  =
  let eb = bodies2vars (external_bodies prg u)
      af =  (falselits assig spvars)
  in
  if ((intersect eb af )==eb)
  then (spc, s, u, True)                                                       -- unfounded set found
  else
    let
      
      (BLit b) = (head (eb \\ af))
      pb = atomsfromvar (BLit b)
      scc_p = (scc p (pos_dep_graph prg))
    in
    if ((intersect pb (intersect scc_p s))==[])
    then
      let (spc2, remove) = (shrink_u prg spc u (BLit b))
          u2 = (u \\ remove)
          s2 = (s \\ remove)
      in
      (loop_u 1 nums prg spc2 assig spvars s2 u2 p)
    else
      let u2 = u ++ (intersect pb (intersect scc_p s)) in
      (loop_u 1 nums prg spc assig spvars s u2 p)


shrink_u:: [Rule] -> SPC -> [Atom] ->  SPVar -> (SPC, [Atom])
-- returns an updated spc and a list of atoms to be removed from U and S
shrink_u prg spc [] l = (spc,[])
shrink_u prg spc (q:qs) l =
  if (elem l (bodies2vars (bodies prg q)))
  then
    let (spcn,remove) = (shrink_u prg spc qs l)  in
    ((add_source spcn q l), (q:remove))
  else (shrink_u prg spc qs l)
  
-- ------------------------------------------------------------------------------------

-- Conflict Driven Nogood Learning - Enumeration

type DLT = [(Int,AssignedVar)]                                                    -- DecisionLevelTracker

get_dlevel:: DLT -> AssignedVar -> Int
get_dlevel ((i,sl1):xs) sl2
  | sl1 == sl2 = i
  | otherwise = get_dlevel xs sl2

get_dliteral:: DLT -> Int -> AssignedVar
get_dliteral ((i1,sl):xs) i2
  | i1 == i2 = sl
  | otherwise = get_dliteral xs i2



cdnl_enum:: [Rule] -> Int -> [[Atom]]
cdnl_enum prg s =
  let cngs = (nub (nogoods_of_lp prg))
      vars = get_vars cngs
      l = length vars
      assi = [0 | x <- [1..l]]
      ngs =  transforms cngs vars
  in
  cdnl_enum_loop prg 0 0 0 [] [] ngs [] assi vars


cdnl_enum_loop:: [Rule] -> Int -> Int -> Int -> DLT -> [(Int,AssignedVar)] -> [Clause] -> [Clause] -> Assignment -> [SPVar] -> [[Atom]]
cdnl_enum_loop prg s dl bl dlt dliteral ngs_p ngs assig spvars =
  let
    (maybeassig,ngs2,sat,dlt2) = ng_prop prg dl dlt ngs_p ngs assig spvars []
  in
  case maybeassig of
       ASSIGNMENT assig2 -> -- no conflict
                            let
                                selectable = get_unassigned assig2
                            in
                            if (selectable==[])
                            then                                                                        -- if all atoms then answer set found
                              let s2= s-1 in
                              if (dl==0 || s2==0)
                              then                                                                     -- last answer set
                                [nub (trueatoms assig2 spvars)]
                              else                                                                     -- backtrack for remaining answer sets
                                let
                                    sigma_d = (get_dliteral dliteral (dl))
                                    dl2 = dl-1
                                    bl2 = dl2
                                    dliteral2 = dlbacktrack dliteral dl
                                    assig3 = backtrack assig2 dlt2 dl
                                    dlt3 = dlbacktrack dlt2 dl
                                    assig4 = assign assig3 (invert sigma_d)                         -- invert last decision literal
                                    dlt4 = ((dl2,(invert sigma_d)): dlt3)
                                    remaining_as = cdnl_enum_loop prg s2 dl2 bl2 dlt4 dliteral2 ngs_p ngs2 assig4 spvars
                                in
                                ((nub (trueatoms assig2 spvars)):remaining_as)
                            else                                                                        -- select new lit
                              let sigma_d = head selectable
                                  dltn = (((dl+1),(T sigma_d)):dlt2)                                    -- extend assignment
                                  dliteral2 = (((dl+1),(T sigma_d)):dliteral)
                                  assig3 = assign assig2 (T sigma_d)
                              in
                              cdnl_enum_loop prg s (dl+1) bl dltn dliteral2 ngs_p ngs2 assig3 spvars

       Conflict ccl cass ->   -- conflict
                            if dl==0
                            then []                                                                     -- no more answer sets
                            else                                                                        -- conflict analysis and backtrack
                              if (bl < dl)
                              then

                                let (nogood, sigma_uip, dl3) = conflict_analysis  dlt2 (ngs_p++ngs2) ccl cass
                                    ngs3 = (nogood:ngs2)
                                    assig3 = assign (backtrack cass dlt2 dl3) sigma_uip
                                in
                                cdnl_enum_loop prg s dl3 bl dlt2 dliteral ngs_p ngs3 assig3 spvars
                              else
                                let sigma_d = (get_dliteral dliteral (dl))
                                    dl2 = dl-1
                                    bl2 = dl2
                                    assig3 = assign (backtrack cass dlt2 dl2) (invert sigma_d)
                                    dlt3 = ((dl2,(invert sigma_d)):dlt2)
                                    remaining_as = cdnl_enum_loop prg s dl2 bl2 dlt3 dliteral ngs_p ngs2 assig3 spvars
                                in
                                remaining_as



dlbacktrack:: DLT -> Int -> DLT
-- backtracks the decision levels
dlbacktrack dlt dl = [ (l,sl) | (l,sl) <- dlt, l < dl ]


backtrack:: Assignment -> DLT -> Int -> Assignment
backtrack assig dlt dl = backtrack2 assig 1 dlt dl
backtrack2 [] _ dlt dl = []
backtrack2 (0:as) n dlt dl = (0:(backtrack2 as (n+1) dlt dl))
backtrack2 (1:as) n dlt dl = 
  if ((get_dlevel dlt (T n)) < dl)
  then (1:(backtrack2 as (n+1) dlt dl))
  else (0:(backtrack2 as (n+1) dlt dl))
backtrack2 ((-1):as) n dlt dl =  
  if ((get_dlevel dlt (F n)) < dl)
  then ((-1):(backtrack2 as (n+1) dlt dl))
  else (0:(backtrack2 as (n+1) dlt dl))



conflict_analysis:: DLT -> [Clause] -> Clause -> Assignment -> (Clause, AssignedVar, Int)
conflict_analysis  dlt nogoods nogood assig =
  let c = get_first_assigned_var assig
      nextassig = unassign assig c
  in
  if elemClause c nogood
  then
    let reduced_nogood = clauseWithoutSL nogood c
        sigma = c
        dl_sigma = get_dlevel dlt sigma
        (t,f)=nogood
        rho = ([ (T l) | l<-t, (get_dlevel dlt (T l))==dl_sigma ] ++ [ (F l) | l<-f, (get_dlevel dlt (F l))==dl_sigma ])
    in
    if (length rho)==1
    then
      let (t,f) = reduced_nogood
          k = maximum( (map (get_dlevel dlt) (map T t)) ++ (map (get_dlevel dlt) (map F f))++ [0])
      in  
      (nogood, sigma, k)
    else
      let
        eps = get_epsilon nogoods sigma nextassig
        reduced_eps = clauseWithoutSL eps (invert sigma)
        newnogood = joinClause reduced_nogood reduced_eps
      in
      conflict_analysis dlt nogoods newnogood nextassig

  else conflict_analysis dlt nogoods nogood nextassig


get_epsilon:: [Clause] -> AssignedVar -> Assignment -> Clause
get_epsilon [] l prefix = ([],[]) --error ?

get_epsilon (ng:ngs) (T sigma) prefix =
  let temp = without ng prefix in
  if ( temp == ([],[sigma]) )
  then
  ng
  else (get_epsilon ngs (T sigma) prefix)

get_epsilon (ng:ngs) (F sigma) prefix =
  let temp = without ng prefix in
  if ( temp == ([sigma],[]) )
  then ng
  else (get_epsilon ngs (F sigma) prefix)

-- -----------------------------------------------------------------------------------------------

-- Propagation
  
data PropRes =  ASSIGNMENT Assignment  -- result of propagation can either be a conflict or a new assignment
         | Conflict Clause Assignment
         deriving (Show,Eq)
  

ng_prop::  [Rule] -> Int -> DLT -> [Clause] -> [Clause] -> Assignment -> [SPVar] -> [Atom] -> (PropRes,[Clause],Bool,DLT)
ng_prop prg dl dlt ngs_p ngs assig spvars u =
  let
    spc = emptyspc
    (maybeassig,dlt2) = (local_propagation prg dl dlt (ngs_p++ngs) assig)
  in    
  case maybeassig of                                                           -- TODO if prg is tight skip unfounded set check
       ASSIGNMENT assig2 -> let
                                u2 = u \\ (falseatoms assig2 spvars)
                            in
                            if (u2 == [])
                            then                                               -- unfounded set check
                              let u3 = (unfounded_set prg spc assig2 spvars) in
                              if (u3==[])
                              then (ASSIGNMENT assig2, ngs, True, dlt2)
                              else                                             -- learn loop nogood
                                let 
				    p = get_svar ((ALit (head u3))) spvars
                                in
				if (elemAss (T p) assig2)
                                then 
                                  let cngs_of_loop = (loop_nogoods prg u3)
				      ngs_of_loop = transforms cngs_of_loop spvars
				  in
                                  (ASSIGNMENT assig2,(ngs_of_loop++ngs),True,dlt2)
                                else
                                  let
                                    assig3 = assign assig2 (F p)               -- extend assignment
                                    dltn = ((dl,(F p)):dlt2)
                                  in
                                  case elemAss (F p) assig2 of
                                    True  -> ng_prop prg dl dlt2 ngs_p ngs assig2 spvars u3
                                    False -> ng_prop prg dl dltn ngs_p ngs assig3 spvars u3
                            else                                               -- learn loop nogood from u2
                              let
				  p = get_svar ((ALit (head u2))) spvars
				  cngs_of_loop = (loop_nogoods prg u2)
                                  ngs2 = (transforms cngs_of_loop spvars) ++ngs
                              in
			      if (elemAss (T p) assig2) 
                              then (ASSIGNMENT assig2, ngs2, True, dlt2)
                              else
                                let
                                  assig3 = assign assig2 (F p)       -- extend assignment
                                  dltn = ((dl,(F p)):dlt2)               
                                in
                                if (elemAss (F p) assig2)
                                then
                                  ng_prop prg dl dlt2 ngs_p ngs2 assig2 spvars u2
                                else
                                  ng_prop prg dl dltn ngs_p ngs2 assig3 spvars u2
                                  
       Conflict ccl cass    -> (Conflict ccl cass, ngs, False, dlt2)           -- return conflic clause


local_propagation::  [Rule] -> Int -> DLT -> [Clause] -> Assignment -> (PropRes,DLT)
-- takes a program a set of nogoods and an assignment and returns a new assignment
local_propagation p dl dlt nogoods assig =
  let (up,dlt2) = unitpropagate dl dlt assig nogoods
  in
  case up of
    ASSIGNMENT newassig -> if newassig == assig                         
                             then (ASSIGNMENT assig,dlt2)                      -- return new assignment
                             else local_propagation  p dl dlt2 nogoods newassig
    Conflict ccl cass   -> (Conflict ccl cass,dlt2)                            -- return conflict clause


unitpropagate:: Int -> DLT -> Assignment -> [Clause] -> (PropRes,DLT)
unitpropagate dl dlt assig [] = (ASSIGNMENT assig, dlt)

unitpropagate dl dlt assig (ng:ngs) =
  let x = unitresult dl dlt assig ng in
  case x of
    (ASSIGNMENT assig2,dlt2) -> unitpropagate dl dlt2 assig2 ngs            
    (Conflict ccl cass,dlt2)        -> (Conflict ccl cass,dlt)                            -- return conflict clause


unitresult:: Int -> DLT -> Assignment -> Clause -> (PropRes,DLT)     
unitresult dl dlt assig nogood =
  case (without nogood assig) of
    ([],[])  -> (Conflict nogood assig,dlt)
    ([l],[]) -> let dlt2 = ((dl,(F l)):dlt) in
		if isassigned l assig
                then (ASSIGNMENT assig, dlt)
		else (ASSIGNMENT (assign assig (F l)),dlt2)
    ([],[l]) -> let dlt2 = ((dl,(T l)):dlt) in
		if isassigned l assig
                then (ASSIGNMENT assig, dlt)    
		else (ASSIGNMENT (assign assig (T l)),dlt2)
    _        -> (ASSIGNMENT assig,dlt)                                             -- nothing can be derived
    
