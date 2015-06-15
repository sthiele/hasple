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

-- import Debug.Trace
import ASP
import SPVar
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

cn p =
   if (reducebasicprogram p (facts p)) == p
   then (facts p)
   else nub ((facts p) ++ (cn (reducebasicprogram p (facts p))))


reduct:: [Rule] -> [Atom] -> [Rule]
-- return the reduct of a logic program with x
reduct p x = [ (basicRule (kopf r) (pbody r)) |  r <- p,  (intersect (nbody r) x)==[] ]


anssets:: [Rule] -> [[Atom]]

anssets p = filter (\i -> (sort (cn (reduct p i)))==(sort i)) (subsets (heads_p p))


-- --------------------------------------------------------------------------------


get_svar:: SPVar -> [SPVar] -> SVar
get_svar l x = get_svar2 l x 0

get_svar2:: SPVar -> [SPVar] -> Int -> SVar
get_svar2 s (f:ls) n =
  if s==f
  then n
  else get_svar2 s ls (n+1)


transforms:: [CClause] -> [SPVar] -> [Clause]

transforms [] _ = []

transforms (c:cs) spvars = ((transform c spvars):(transforms cs spvars))


transform:: CClause -> [SPVar] -> Clause
transform (t,f) spvars = ((transf2 t spvars), (transf2 f spvars))

transf2:: [SPVar] -> [SPVar] -> [SVar]
transf2 [] _ = []

transf2 (spv:spvs) l = ((get_svar spv l):(transf2 spvs l))


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
   if elem a visited
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
  not (null scc_a)


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
  if (intersect eb af)==eb
  then (spc, s, u, True)                                                       -- unfounded set found
  else
    let

      (BLit b) = (head (eb \\ af))
      pb = atomsfromvar (BLit b)
      scc_p = (scc p (pos_dep_graph prg))
    in
    if null (intersect pb (intersect scc_p s))
    then
      let (spc2, remove) = (shrink_u prg spc u (BLit b))
          u2 = (u \\ remove)
          s2 = (s \\ remove)
      in
      loop_u 1 nums prg spc2 assig spvars s2 u2 p
    else
      let u2 = u ++ (intersect pb (intersect scc_p s)) in
      loop_u 1 nums prg spc assig spvars s u2 p


shrink_u:: [Rule] -> SPC -> [Atom] ->  SPVar -> (SPC, [Atom])
-- returns an updated spc and a list of atoms to be removed from U and S
shrink_u prg spc [] l = (spc,[])

shrink_u prg spc (q:qs) l =
  if elem l (bodies2vars (bodies prg q))
  then
    let (spcn,remove) = (shrink_u prg spc qs l)  in
    ((add_source spcn q l), (q:remove))
  else shrink_u prg spc qs l

-- ------------------------------------------------------------------------------------

-- Conflict Driven Nogood Learning - Enumeration

type DLT = [(Int,SignedVar)]                                                    -- DecisionLevelTracker

get_dlevel:: DLT -> SignedVar -> Int

get_dlevel ((i,sl1):xs) sl2
  | sl1 == sl2 = i
  | otherwise = get_dlevel xs sl2

get_dliteral:: DLT -> Int -> SignedVar

get_dliteral ((i1,sl):xs) i2
  | i1 == i2 = sl
  | otherwise = get_dliteral xs i2



cdnl_enum:: [Rule] -> Int -> [[Atom]]

cdnl_enum prg s =
  let cngs = (nub (nogoods_of_lp prg))
      vars = get_vars cngs
      l = length vars
      assi = initialAssignment l
      ngs =  transforms cngs vars
  in
  cdnl_enum_loop prg 0 1 0 [] [] ngs [] assi vars


cdnl_enum_loop:: [Rule] -> Int -> Int -> Int -> DLT -> [(Int,SignedVar)] -> [Clause] -> [Clause] -> Assignment -> [SPVar] -> [[Atom]]

cdnl_enum_loop prg s dl bl dlt dliteral ngs_p ngs assig spvars =
  let
    (maybeassig,ngs2,dlt2) = ng_prop prg dl dlt ngs_p ngs assig spvars []
  in
  case maybeassig of
       ASSIGNMENT assig2 -> -- no conflict
                            let
                                selectable = get_unassigned assig2
                            in
                            if null selectable
                            then                                                                        -- if all atoms then answer set found
                              let s2= s-1 in
                              if (dl==1 || s2==0)
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
                                    assig4 = assign assig3 (invert sigma_d) dl2                         -- invert last decision literal
                                    dlt4 = ((dl2,(invert sigma_d)): dlt3)
                                    remaining_as = cdnl_enum_loop prg s2 dl2 bl2 dlt4 dliteral2 ngs_p ngs2 assig4 spvars
                                in
                                ((nub (trueatoms assig2 spvars)):remaining_as)
                            else                                                                        -- select new lit
                              let sigma_d = head selectable
                                  dltn = (((dl+1),(T sigma_d)):dlt2)                                    -- extend assignment
                                  dliteral2 = (((dl+1),(T sigma_d)):dliteral)
                                  assig3 = assign assig2 (T sigma_d) (dl+1)
                              in
                              cdnl_enum_loop prg s (dl+1) bl dltn dliteral2 ngs_p ngs2 assig3 spvars

       Conflict ccl cass ->   -- conflict
                            if dl==1
                            then []                                                                     -- no more answer sets
                            else                                                                        -- conflict analysis and backtrack
                              if bl < dl
                              then
                                let (nogood, sigma_uip, dl3) = conflict_analysis  dlt2 (ngs_p++ngs2) ccl cass
                                    ngs3 = (nogood:ngs2)
                                    assig3 = assign (backtrack cass dlt2 dl3) sigma_uip 1
                                in
                                cdnl_enum_loop prg s dl3 bl dlt2 dliteral ngs_p ngs3 assig3 spvars
                              else
                                let sigma_d = (get_dliteral dliteral (dl))
                                    dl2 = dl-1
                                    bl2 = dl2
                                    assig3 = assign (backtrack cass dlt2 dl2) (invert sigma_d) dl2
                                    dlt3 = ((dl2,(invert sigma_d)):dlt2)
                                    remaining_as = cdnl_enum_loop prg s dl2 bl2 dlt3 dliteral ngs_p ngs2 assig3 spvars
                                in
                                remaining_as



dlbacktrack:: DLT -> Int -> DLT
-- backtracks the decision levels
dlbacktrack dlt dl = [ (l,sl) | (l,sl) <- dlt, l < dl ]


backtrack:: Assignment -> DLT -> Int -> Assignment
backtrack a [] dl = a

backtrack a ((l,lit):dlt) dl =
  if l < dl
  then a
  else backtrack (unassign a lit) dlt dl





conflict_analysis:: DLT -> [Clause] -> Clause -> Assignment -> (Clause, SignedVar, Int)
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


get_epsilon:: [Clause] -> SignedVar -> Assignment -> Clause

get_epsilon [] l prefix = ([],[]) --error ?

get_epsilon (ng:ngs) (T sigma) prefix =
  let temp = without ng prefix in
  if temp == ([],[sigma])
  then ng
  else (get_epsilon ngs (T sigma) prefix)

get_epsilon (ng:ngs) (F sigma) prefix =
  let temp = without ng prefix in
  if temp == ([sigma],[])
  then ng
  else (get_epsilon ngs (F sigma) prefix)

-- -----------------------------------------------------------------------------------------------

add_assigs:: DLT -> [SVar] -> [SVar] -> Int -> DLT
add_assigs dlt truelits falselits dl =
  add_fassigs (add_tassigs dlt truelits dl) falselits dl

add_tassigs:: DLT -> [SVar] -> Int -> DLT
add_tassigs dlt [] _ = dlt
add_tassigs dlt (l:ls) dl =
  add_tassigs ((dl,(T l)):dlt) ls dl

add_fassigs:: DLT -> [SVar] -> Int -> DLT
add_fassigs dlt [] _ = dlt
add_fassigs dlt (l:ls) dl =
  add_fassigs ((dl,(F l)):dlt) ls dl

-- Propagation

data PropRes =  ASSIGNMENT Assignment  -- result of propagation can either be a conflict or a new assignment
         | Conflict Clause Assignment
         deriving (Show,Eq)


ng_prop::  [Rule] -> Int -> DLT -> [Clause] -> [Clause] -> Assignment -> [SPVar] -> [Atom] -> (PropRes,[Clause],DLT)

ng_prop prg dl dlt ngs_p ngs assig spvars u =
  let
    spc = emptyspc
    nogoods= ngs_p++ngs
    (maybeassig,dlt2) = (local_propagation prg dl dlt (cycle nogoods) 0 (length nogoods) assig)
  in
  case maybeassig of                                                           -- TODO if prg is tight skip unfounded set check
       ASSIGNMENT assig2 -> let u2 = u \\ (falseatoms assig2 spvars) in
                            if null u2
                            then                                               -- unfounded set check
                              let u3 = (unfounded_set prg spc assig2 spvars) in
                              if null u3
                              then (ASSIGNMENT assig2, ngs, dlt2)
                              else                                             -- learn loop nogood
                                let
				    p = get_svar ((ALit (head u3))) spvars
                                in
				if elemAss (T p) assig2
                                then
                                  let cngs_of_loop = (loop_nogoods prg u3)
				      ngs_of_loop = transforms cngs_of_loop spvars
				  in
                                  (ASSIGNMENT assig2,(ngs_of_loop++ngs),dlt2)
                                else
                                  let
                                    assig3 = assign assig2 (F p)  dl              -- extend assignment
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
			      if elemAss (T p) assig2
                              then (ASSIGNMENT assig2, ngs2,  dlt2)
                              else
                                let
                                  assig3 = assign assig2 (F p) dl      -- extend assignment
                                  dltn = ((dl,(F p)):dlt2)
                                in
                                if (elemAss (F p) assig2)
                                then
                                  ng_prop prg dl dlt2 ngs_p ngs2 assig2 spvars u2
                                else
                                  ng_prop prg dl dltn ngs_p ngs2 assig3 spvars u2

       Conflict ccl cass -> (Conflict ccl cass, ngs, dlt2)           -- return conflic clause


local_propagation::  [Rule] -> Int -> DLT -> [Clause] -> Int -> Int -> Assignment -> (PropRes,DLT)
-- takes a program a cyclic list of nogoods and an assignment and returns a propagation result
local_propagation p dl dlt (ng:nogoods) done todo assig =
  let (up,dlt2) = unitresult dl dlt assig ng
  in
  case up of
    ASSIGNMENT newassig -> if newassig == assig
                           then
                             if (done+1) == todo
                             then (ASSIGNMENT assig,dlt2)                      -- return new assignment
                             else local_propagation  p dl dlt2 nogoods (done+1) todo assig
                           else local_propagation  p dl dlt2 nogoods 0 todo newassig
    Conflict ccl cass   -> (Conflict ccl cass,dlt)                             -- return conflict clause


unitresult:: Int -> DLT -> Assignment -> Clause -> (PropRes,DLT)

unitresult dl dlt assig nogood =
  case (without nogood assig) of
    ([],[])  -> (Conflict nogood assig,dlt)
    ([l],[]) -> let dlt2 = ((dl,(F l)):dlt) in
		if isassigned l assig
                then (ASSIGNMENT assig, dlt)
                else (ASSIGNMENT (assign assig (F l) dl),dlt2)
    ([],[l]) -> let dlt2 = ((dl,(T l)):dlt) in
		if isassigned l assig
                then (ASSIGNMENT assig, dlt)
                else (ASSIGNMENT (assign assig (T l) dl),dlt2)
    _        -> (ASSIGNMENT assig,dlt)                                             -- nothing can be derived

