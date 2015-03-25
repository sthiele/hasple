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
import Data.List (sort, nub, intersect, (\\), delete )
import Data.Maybe 
-- import Data.List.Extra (nubOrd)
-- use sort to order list nub (nubOrd) to remove duplicates from list -- maybe use Sets instead?
import qualified Data.Map as Map


-- --------------------------------------------------------------


subsets :: [a] -> [[a]]
subsets []  = [[]]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)


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


-- --------------------------------------------------------------------------------

data Lit = ALit Atom
         | BLit [Atom] [Atom]
         deriving (Show,Eq,Ord)

__bottom = (ALit __conflict)
           
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


data SignedLit = T Lit
         | F Lit
         deriving (Show,Eq,Ord)

unsign:: SignedLit -> Lit
unsign (T l) = l
unsign (F l) = l

invert:: SignedLit -> SignedLit
invert (T l) = (F l)
invert (F l) = (T l)

type Assignment = ([Lit],[Lit])

joinAss:: Assignment -> Assignment -> Assignment
joinAss (t1,f1) (t2,f2) = ( (t1++t2),(f1++f2))

extendAss:: Assignment -> SignedLit -> Assignment
extendAss (ts,fs) (T l) = ((l:ts),fs)
extendAss (ts,fs) (F l) = (ts,(l:fs))

without:: Assignment -> Assignment -> Assignment
without (t1,f1) (t2,f2) = ( (t1\\t2),(f1\\f2))

withoutSL:: Assignment -> SignedLit -> Assignment
withoutSL (t,f) (T l) = ((delete l t),f)
withoutSL (t,f) (F l) = (t,(delete l f))

signedLits:: Assignment -> [SignedLit]
signedLits (t,f) = [ (T l) | l<-t ] ++ [ (F l) | l<-f ]

elemAss:: SignedLit -> Assignment -> Bool
elemAss (T l) (t,_) = elem l t
elemAss (F l) (_,f) = elem l f


type Clause = Assignment

assignment2lits:: Assignment -> [Lit]
assignment2lits (t,f) = (t++f)

truelits:: Assignment -> [Lit]
truelits (t,_) = t

falselits:: Assignment -> [Lit]
falselits (_,f) = f

trueatoms:: Assignment -> [Atom]
trueatoms (t,_) = concatMap lit2atoms t

falseatoms:: Assignment -> [Atom]
falseatoms (_,f) = concatMap lit2atoms f

lit2atoms:: Lit -> [Atom]
lit2atoms (ALit a) = [a]
lit2atoms (BLit pb nb) = pb

-- ---------------------------------------------------------------------------------
-- no_good generation


nogoods_of_lp:: [Rule] -> [Clause]
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


get_ng1:: ([Atom],[Atom]) -> Clause
get_ng1 (pb,nb) =
  ((atoms2lits pb), ((BLit pb nb):(atoms2lits nb)))


get_ng2:: ([Atom],[Atom]) -> [Clause]
get_ng2 (pb,nb) =
  let
    clauses1 = [ ([(BLit pb nb)],[(ALit atom)]) | atom <- pb ]
    clauses2 = [ ([(BLit pb nb),(ALit atom)],[]) | atom <- nb ]
  in
  clauses1 ++ clauses2

get_ng3:: [Rule] -> Atom -> [Clause]
get_ng3 p a = [ ([(BLit pb nb)], [(ALit a)]) | (pb,nb) <- (bodies p a) ]

get_ng4:: [Rule] -> Atom -> Clause
get_ng4 p a = ([(ALit a)], (bodies2lits (bodies p a)))


external_bodies:: [Rule] -> [Atom] -> [([Atom],[Atom])]
-- returns the external bodies
external_bodies p u =
  [ ((pbody r),(nbody r)) |  r <- p, elem (kopf r) u, (intersect (pbody r) u)==[] ]


loop_nogood:: Atom -> [([Atom],[Atom])] -> Clause
-- returns the loop nogood for an atom in an unfounded set(characterized by the external bodies)
loop_nogood a bodies = ([(ALit a)], (bodies2lits bodies))

loop_nogoods:: [Rule] -> [Atom] -> [Clause]
-- return the loop nogoods of the program for a given unfounded set
loop_nogoods p u = [ (loop_nogood atom (external_bodies p u)) | atom<-u  ]


-- ---------------------------------------------------------------------------------
-- unfounded set checker

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
-- returns the strongly connected component of an atom
scc a depg = nub (tarjan depg [] [] a)

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



type SourcePointerConf =   (Map.Map Atom Lit)
emptyspc:: SourcePointerConf
emptyspc = Map.empty



add_source::  SourcePointerConf -> Atom -> Lit -> SourcePointerConf
-- add a new sourcep for an atom
add_source spc a l =  Map.insert a l spc

source:: Atom -> SourcePointerConf -> Lit
source a spc =
   case Map.lookup a spc of
       Nothing -> __bottom
       Just x  ->  x

sourcep:: Atom -> SourcePointerConf -> [Atom]
sourcep a spc =
  case (source a spc) of
  (BLit pb nb) ->  pb
  __bottom -> []
  

cyclic:: Atom -> [Rule] -> Bool
-- test if an atom has a cyclic definition might be easier, if scc\=[]
cyclic a p =
  let scc_a = scc a (pos_dep_graph p) in
  not (scc_a == [])


unfounded_set:: [Rule] -> SourcePointerConf -> Assignment -> [Atom]
-- returns an unfounded set for the program given a partial assignment
unfounded_set prg spc assig =
  let s = collect_nonfalse_cyclic_atoms assig prg
      s2 = extend prg assig spc s                                               -- bis line 5
  in
  loop_s 0 prg spc assig s2

  
collect_nonfalse_cyclic_atoms:: Assignment -> [Rule] -> [Atom]
collect_nonfalse_cyclic_atoms assig p =
  let atoms = nub (atoms_p p) \\ (falseatoms assig)
  in
  [ a | a <- atoms, (cyclic a p)]


extend:: [Rule] -> Assignment -> SourcePointerConf -> [Atom]  -> [Atom]
extend p assig spc s =
  let
    helper1 =  (falseatoms assig)++s
    atoms = (atoms_p p)
    helper2 = atoms \\ helper1
    t =[ a | a <- helper2, (intersect (sourcep a spc) (intersect (scc a (pos_dep_graph p)) s)) /= [] ]
  in
    if t==[]
    then s++t
    else extend p assig spc (s++t)

  
loop_s:: Int -> [Rule] -> SourcePointerConf -> Assignment ->[Atom] -> [Atom]
loop_s num prg spc assig [] = []                                                -- no unfounded_set
loop_s num prg spc assig s =
  let u = head s
      eb = bodies2lits (external_bodies prg [u])
      (spc2,s2,u2,found) = loop_u 0 num prg spc assig s [u] u
  in
  if found
  then u2
  else
    loop_s 1 prg spc2 assig s2
  

loop_u:: Int-> Int -> [Rule] -> SourcePointerConf -> Assignment -> [Atom] -> [Atom] -> Atom -> (SourcePointerConf, [Atom], [Atom], Bool)
loop_u num nums prg spc assig s [] p  = (spc, s, [], False)
loop_u num nums prg spc assig s u p  =
  let eb = bodies2lits (external_bodies prg u)
      af =  falselits assig 
  in
  if ((intersect eb af )==eb)
  then (spc, s, u, True)                                                        -- unfounded set found
  else
    let
      (BLit pb nb) = (head (eb \\ af))
      scc_p = (scc p (pos_dep_graph prg))
    in
    if ((intersect pb (intersect scc_p s))==[])
    then
      let (spc2, remove) = (shrink_u prg spc u (BLit pb nb))
          u2 = (u \\ remove)
          s2 = (s \\ remove)
      in
      (loop_u 1 nums prg spc2 assig s2 u2 p)
    else
      let u2 = u ++ (intersect pb (intersect scc_p s)) in
      (loop_u 1 nums prg spc assig s u2 p)
      
    
shrink_u:: [Rule] -> SourcePointerConf -> [Atom] ->  Lit -> (SourcePointerConf, [Atom])
-- returns an updated spc and a list of atoms to be removed from U and S
shrink_u prg spc [] l = (spc,[])
shrink_u prg spc (q:qs) l =
  if (elem l (bodies2lits (bodies prg q)))
  then
    let (spcn,remove) = (shrink_u prg spc qs l)  in
    ((add_source spcn q l), (q:remove))
  else (shrink_u prg spc qs l)


  
-- ------------------------------------------------------------------------------------
-- cdnl_enum

type DLT = [(Int,SignedLit)]                                                    -- DecisionLevelTracker

get_dlevel:: [(Int,SignedLit)] -> SignedLit -> Int
get_dlevel ((i,sl1):xs) sl2
  | sl1 == sl2 = i
  | otherwise = get_dlevel xs sl2

get_dliteral:: [(Int,SignedLit)] -> Int -> SignedLit
get_dliteral ((i1,sl):xs) i2
  | i1 == i2 = sl
  | otherwise = get_dliteral xs i2
  
  
cdnl_enum:: [Rule] -> Int -> [[Atom]]
cdnl_enum prg s = cdnl_enum_loop prg 0 0 0 [] [] (nub (nogoods_of_lp prg)) [] ([],[])
    
cdnl_enum_loop:: [Rule] -> Int -> Int -> Int -> DLT -> [(Int,SignedLit)] -> [Clause] -> [Clause] -> Assignment -> [[Atom]]
cdnl_enum_loop prg s dl bl dlt dliteral ngs_p ngs assig  =
  let
    (assig2,ngs2,sat,dlt2) = ng_prop prg dl dlt ngs_p ngs assig []
  in
  if sat
  then                                                                          -- no conflict
    let
        all_lits = nub ((bodies2lits(bodies_p prg)) ++ (atoms2lits (atoms_p prg)))
        selectable = (all_lits \\ (assignment2lits (assig2)))      
    in
    if (selectable==[])
    then                                                                        -- if all atoms then answer set found
       let s2= s-1 in
       if (dl==0 || s2==0)
       then                                                                     -- last answer set
         [nub (trueatoms assig2)]
       else                                                                     -- backtrack for remaining answer sets
         let
             sigma_d = (get_dliteral dliteral (dl))
             dl2 = dl-1
             bl2 = dl2
             dliteral2 = dlbacktrack dliteral dl
             assig3 = backtrack assig2 dlt2 dl
             dlt3 = dlbacktrack dlt2 dl
             assig4 = extendAss assig3 (invert sigma_d)                         -- invert last decision literal
             dlt4 = ((dl2,(invert sigma_d)): dlt3)
             remaining_as = cdnl_enum_loop prg s2 dl2 bl2 dlt4 dliteral2 ngs_p ngs2 assig4
         in
         ((nub (trueatoms assig2)):remaining_as)
    else                                                                        -- select new lit
      let sigma_d = head selectable
          dltn = (((dl+1),(T sigma_d)):dlt2)                                    -- extend assignment
          dliteral2 = (((dl+1),(T sigma_d)):dliteral)
--           assig3 = ((T sigma_d):assig2)
          assig3 = extendAss assig2 (T sigma_d)
      in
      cdnl_enum_loop prg s (dl+1) bl dltn dliteral2 ngs_p ngs2 assig3
  else                                                                          -- conflict
    if dl==0
    then []                                                                     -- no more answer sets
    else                                                                        -- conflict analysis and backtrack
      if (bl < dl)
      then
        let [cf] = ngs2
            (nogood, dl3) = conflict_analysis  dlt2 (ngs_p++ngs) cf assig2
            ngs3 = (nogood:ngs)
            assig3 = backtrack assig2 dlt2 dl3
        in
        cdnl_enum_loop prg s dl3 bl dlt2 dliteral ngs_p ngs3 assig3
      else
         let sigma_d = (get_dliteral dliteral (dl))
             dl2 = dl-1
             bl2 = dl2
             assig3 = extendAss (backtrack assig2 dlt2 dl2) (invert sigma_d)
             dlt3 = ((dl2,(invert sigma_d)):dlt2)
             remaining_as = cdnl_enum_loop prg s dl2 bl2 dlt3 dliteral ngs_p ngs2 assig3
         in
         remaining_as


dlbacktrack:: DLT -> Int -> DLT
-- backtracks the decision levels
dlbacktrack dlt dl = [ (l,sl) | (l,sl) <- dlt, l < dl ]


backtrack:: Assignment -> DLT -> Int -> Assignment
-- backtracks an assignment
backtrack (t,f) dlt dl =
  ([ l | l <- t, (get_dlevel dlt (T l)) < dl ], [ l | l <- f, (get_dlevel dlt (F l)) < dl ] )
  
         

conflict_analysis:: DLT -> [Clause] -> Clause -> Assignment -> (Clause, Int)
conflict_analysis  dlt nogoods nogood assig =
  let (prefix, sigma) = (get_sigma nogood assig)
      ng_sans_sigma = withoutSL nogood sigma
      dls = (map (get_dlevel dlt) (signedLits ng_sans_sigma))++[0]
      k = maximum dls
  in
  if (k == (get_dlevel dlt sigma))
  then
    let eps = get_epsilon nogoods sigma prefix
        nogood2 = joinAss ng_sans_sigma (withoutSL eps (invert sigma))
        
    in
    (conflict_analysis  dlt nogoods nogood2 assig)

  else (nogood, k)


get_sigma:: Clause -> Assignment -> (Assignment, SignedLit)
get_sigma nogood ([],[]) = let s = (show nogood) in
                          (error ("Unknown error in get_sigma "++s))

get_sigma nogood ((t:ts),f) =
  let test = without nogood (ts,f) in
  if (test==([t],[]))
  then ((ts,f), (T t))
  else get_sigma nogood (ts,f)

get_sigma nogood ([],(f:fs)) =
  let test = without nogood ([],fs) in
  if (test==([],[f]))
  then (([],fs), (F f))
  else get_sigma nogood ([],fs)
  

get_epsilon:: [Clause] -> SignedLit -> Assignment -> Clause
get_epsilon [] l prefix = ([],[]) --error ?

get_epsilon (ng:ngs) (T sigma) prefix =
  let temp = without ng prefix in
  if ( temp == ([],[sigma]) )
  then ng
  else (get_epsilon ngs (T sigma) prefix)

get_epsilon (ng:ngs) (F sigma) prefix =
  let temp = without ng prefix in
  if ( temp == ([sigma],[]) )
  then ng
  else (get_epsilon ngs (F sigma) prefix)

  

ng_prop::  [Rule] -> Int -> DLT -> [Clause] -> [Clause] -> Assignment -> [Atom] -> (Assignment,[Clause],Bool,DLT)
ng_prop prg dl dlt ngs_p ngs assig u =
  let
    spc = emptyspc
    (maybeassig,dlt2) = (local_propagation prg dl dlt (ngs_p++ngs) assig)
  in
  case maybeassig of                                                            -- TODO if prg is tight skip unfounded set check
       ASSIGNMENT assig2 -> let
                                u2 = u \\ (falseatoms assig2)
                            in
                            if (u2 == [])
                            then                                                -- unfounded set check
                              let u3 = (unfounded_set prg spc assig2) in
                              if (u3==[])
                              then (assig2,ngs, True,dlt2)
                              else                                              -- learn loop nogood
                                let p = (head u3)
                                in
                                if (elem p (trueatoms assig2))
                                then (assig2,((loop_nogoods prg u3)++ngs),True,dlt2)
                                else
                                  let
                                    assig3 = extendAss assig2 (F (ALit p))      -- extend assignment
                                    dltn = ((dl,(F (ALit p))):dlt2)
                                  in
                                  case elemAss (F (ALit p)) assig2 of
                                    True  -> ng_prop prg dl dlt2 ngs_p ngs assig2 u3
                                    False -> ng_prop prg dl dltn ngs_p ngs assig3 u3
                            else                                                -- learn loop nogood from u2
                              let p = (head u2)
                                  ngs2 = (loop_nogoods prg u2)++ngs
                              in
                              if (elem p (trueatoms assig2))
                              then (assig2,ngs2,True,dlt2)
                              else
                                let
                                  assig3 = extendAss assig2 (F (ALit p))        -- extend assignment
                                  dltn = ((dl,(F (ALit p))):dlt2)               
                                in
                                if (elemAss (F (ALit p)) assig2)
                                then
                                  ng_prop prg dl dlt2 ngs_p ngs2 assig2 u2
                                else
                                  ng_prop prg dl dltn ngs_p ngs2 assig3 u2
                                  
       Conflict cf       -> (assig, [cf], False, dlt2)                          -- return conflic clause

  
data PropRes =  ASSIGNMENT Assignment  -- result of propagation can either be a conflict or a new assignment
         | Conflict Clause
         deriving (Show,Eq)
  
local_propagation::  [Rule] -> Int -> DLT -> [Clause] -> Assignment -> (PropRes,DLT)
-- takes a program a set of nogoods and an assignment and returns a new assignment
local_propagation p dl dlt nogoods assig =
  let (up,dlt2) = unitpropagate dl dlt assig nogoods
  in
  case up of
    ASSIGNMENT newassig -> if newassig == assig                         
                             then (ASSIGNMENT assig,dlt2)                      -- return new assignment
                             else local_propagation  p dl dlt2 nogoods newassig
    Conflict cf         -> (Conflict cf,dlt2)                                  -- return conflict clause


  

unitpropagate:: Int -> DLT -> Assignment -> [Clause] -> (PropRes,DLT)
unitpropagate dl dlt assig [] = (ASSIGNMENT assig, dlt)

unitpropagate dl dlt assig (ng:ngs) =
  let x = unitresult assig ng in
  case x of
    ASSIGNMENT ([l],[]) ->  let dlt2 = ((dl,(T l)):dlt) in
                            if ( elemAss (T l) assig)
                            then
                              unitpropagate dl dlt assig ngs
                            else
                              let assig2 = extendAss assig (T l) in            -- extend assignment
                              unitpropagate dl dlt2 assig2 ngs            
    ASSIGNMENT ([],[l]) ->  let dlt2 = ((dl,(F l)):dlt) in
                            if ( elemAss (F l) assig)
                            then
                              unitpropagate dl dlt assig ngs
                            else
                              let assig2 = extendAss assig (F l) in            -- extend assignment
                              unitpropagate dl dlt2 assig2 ngs                                     

    ASSIGNMENT ([],[])  ->  unitpropagate dl dlt assig ngs
    Conflict cf         ->  (Conflict cf,dlt)                                  -- return conflict clause

    
unitresult:: Assignment -> Clause -> PropRes     
unitresult assig nogood =
  case (without nogood assig) of
    ([],[])  -> Conflict assig
    ([l],[]) -> ASSIGNMENT ([],[l])
    ([],[l]) -> ASSIGNMENT ([l],[])
    _        -> ASSIGNMENT ([],[])                                             -- nothing can be derived
    


