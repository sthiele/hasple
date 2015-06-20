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

import ASP
import SPVar
import Types
import SPC
import UFS
import Data.List (sort, nub, intersect, (\\), delete )
import Data.Maybe
-- import Data.List.Extra (nubOrd)
-- use sort to order list nub (nubOrd) to remove duplicates from list -- maybe use Sets instead?
import qualified Data.Map as Map
import Debug.Trace
is_debug_on= True
mtrace:: String -> a -> a
mtrace s a= if (is_debug_on)  then trace s a else a

-- -----------------------------------------------------------------------------


subsets:: [a] -> [[a]]
subsets []  = [[]]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)


facts:: [Rule] -> [Atom]
-- return the facts of a programm
facts p = [ (kopf r) |  r <- p,  (null (pbody r)), (null (nbody r)) ]


reducebasicprogram:: [Rule] -> [Atom] -> [Rule]
-- reduces a program by  aset of atoms
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


-- -----------------------------------------------------------------------------


get_svar:: SPVar -> [SPVar] -> SVar
get_svar l x = get_svar2 l x 0

get_svar2:: SPVar -> [SPVar] -> Int -> SVar
get_svar2 s (f:ls) n =
  if s==f
  then n
  else get_svar2 s ls (n+1)


get_svarx:: [SPVar] -> SPVar -> SVar
get_svarx x l = get_svar2 l x 0


transforms:: [CClause] -> [SPVar] -> [Clause]

transforms [] _ = []

transforms (c:cs) spvars = ((transform c spvars):(transforms cs spvars))


transform:: CClause -> [SPVar] -> Clause
transform (t,f) spvars =
  let l = length spvars
      a = initialAssignment l
      tsvars = map (get_svarx spvars) t
      fsvars = map (get_svarx spvars) f
      assi =   assign_trues (assign_falses a fsvars) tsvars
  in
  assi

assign_trues:: Clause -> [SVar] -> Clause
assign_trues a [] = a
assign_trues a (v:vs) = assign_trues (assign a (T v) 1) vs

assign_falses:: Clause -> [SVar] -> Clause
assign_falses a [] = a
assign_falses a (v:vs) = assign_falses (assign a (F v) 1) vs


-- -----------------------------------------------------------------------------

-- Conflict Driven Nogood Learning - Enumeration








cdnl_enum:: [Rule] -> Int -> [[Atom]]

cdnl_enum prg s =
  let cngs = (nub (nogoods_of_lp prg))
      vars = get_vars cngs
      l = length vars
      assi = initialAssignment l
      ngs =  transforms cngs vars
  in
  cdnl_enum_loop prg 0 1 1 1 [] [(1,1)] ngs [] assi vars


cdnl_enum_loop::
  [Rule]                   -- the program
  -> Int                   -- s
  -> Int                   -- decision level
  -> Int                   -- blocked level
  -> Int                   -- assignment level
  -> [(Int,SignedVar)]     -- decision level tracker
  -> [(Int,Int)]           -- al2dl
  -> [Clause]              -- program nogoods
  -> [Clause]              -- learned nogoods
  -> Assignment
  -> [SPVar]               -- maging SPVar 2 SVar(Int)
  -> [[Atom]]              -- found answer sets

cdnl_enum_loop prg s dl bl al dliteral alt ngs_p ngs assig spvars =
  let
    (maybeassig,ngs2,al2) = ng_prop prg al ngs_p ngs assig spvars []
  in
  mtrace( "\ncdnl_loop:\n"
  ++ (show spvars) ++ "\n"
  ++ "assig:" ++ (show assig) ++ "\n"
  ++ "dlits: " ++ (show dliteral)++ "\n"
  ++ "al2dl: " ++ (show alt)
  ) $
  case maybeassig of
    Conflict ccl cass -> -- conflict
                         mtrace( "Conf: " ++(show cass) ++ "\n") $
                         if dl==1
                         then []                                                                     -- no more answer sets
                         else                                                                        -- conflict analysis and backtrack
                           if bl < dl
                           then
                             let (learnednogood, sigma_uip, alx) = conflict_analysis alt (ngs_p++ngs2) ccl cass 1
                             in
                             mtrace ("uip:  " ++ (show sigma_uip) ) $
                             mtrace ("found al: " ++ (show alx) ++ " learnednogood: " ++ (show learnednogood) ) $
                             let
                                 dl3 = (al2dl alt alx)
                                 al3 = dl2al alt dl3
                             in
                             mtrace ( "new al: " ++ (show al3) )$
                             let
                                 ngs3 = (learnednogood:ngs2)
                                 assigxxxx=(backtrack cass al3)
                                 assig3 = assign (backtrack cass al3) (invert sigma_uip) (al3)
                             in
                             mtrace ( "btassig: " ++ (show assigxxxx) )$
                             mtrace ( "neassig: " ++ (show assig3) ) $
                             let
                                 dliteral2 = dlbacktrack dliteral dl3
                                 alt2 = albacktrack alt dl3
                             in
                             mtrace ("nedlits: " ++ (show dliteral2) ) $
                             mtrace ("nealt  : " ++ (show alt2) ) $
                             cdnl_enum_loop prg s (dl3-1) bl (al3+1) dliteral2 alt2 ngs_p ngs3 assig3 spvars
                           else
                             let sigma_d = (get_dliteral dliteral (dl))
                                 dl2 = dl-1
                                 bl2 = dl2
                                 al3 = (dl2al alt dl2)
                                 assig3 = assign (backtrack cass al3) (invert sigma_d) al3
                                 alt2 = albacktrack alt dl2
                                 remaining_as = cdnl_enum_loop prg s dl2 bl2 al3 dliteral alt2 ngs_p ngs2 assig3 spvars
                             in
                             remaining_as
    ASSIGNMENT assig2 -> -- no conflict
                         let
                             selectable = get_unassigned assig2
                         in
                         mtrace( "Prop: " ++(show assig2) ++ "\n") $
                         if null selectable
                         then                                                                       -- if all atoms then answer set found
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
                                 alt2 = albacktrack alt dl
                                 assig3 = backtrack assig2 (dl2al alt dl)
                                 assig4 = assign assig3 (invert sigma_d) dl2                         -- invert last decision literal
                                 remaining_as = cdnl_enum_loop prg s2 dl2 bl2 al dliteral2 alt2 ngs_p ngs2 assig4 spvars
                             in
                             ((nub (trueatoms assig2 spvars)):remaining_as)
                         else                                                                        -- select new lit
                           let sigma_d = head selectable
                               dliteral2 = (((dl+1),(T sigma_d)):dliteral)
                               alt2 = ((al2,dl+1):alt)
                               assig3 = assign assig2 (T sigma_d) (al2)
                           in
                           mtrace ("al: " ++ (show al2)) $
                           mtrace ( "choose: " ++ (show (T sigma_d))) $
                           cdnl_enum_loop prg s (dl+1) bl (al2+1) dliteral2 alt2 ngs_p ngs2 assig3 spvars


al2dl:: [(Int,Int)] -> Int -> Int
al2dl ((al1,dl1):rest) al =
  if al<al1
  then al2dl rest al
  else dl1

dl2al:: [(Int,Int)] -> Int -> Int
dl2al ((al1,dl1):rest) dl =
  if dl==dl1
  then al1
  else dl2al rest dl

albacktrack:: [(Int,Int)] -> Int -> [(Int,Int)]
albacktrack alt l = [ (al,dl) | (al,dl) <- alt, dl < l ]

type DLT = [(Int,SignedVar)]                                                    -- DecisionLevelTracker

get_dliteral:: DLT -> Int -> SignedVar

get_dliteral ((i1,sl):xs) i2
  | i1 == i2 = sl
  | otherwise = get_dliteral xs i2

dlbacktrack:: DLT -> Int -> DLT
-- backtracks the decision levels
dlbacktrack dlt dl = [ (l,sl) | (l,sl) <- dlt, l < dl ]





conflict_analysis:: [(Int,Int)] -> [Clause] -> Clause -> Assignment -> Int -> (Clause, SignedVar, Int)
conflict_analysis alt nogoods nogood assig i =
  let (sigma, prefix) = get_sigma nogood assig i
      dl_sigma = get_dlevel_alevel assig sigma
      reduced_nogood = clauseWithoutSL nogood sigma
      k = get_max_dlevel_alevel reduced_nogood assig
      dl = al2dl alt dl_sigma
      al = dl2al alt dl
  in
  mtrace ( "conflict_analysis: " ++ (show nogood) ++ (show assig) ++ (show sigma) ++ (show prefix) ) $
--   mtrace ( "ca: reduced_nogood: "++ (show reduced_nogood)) $
  mtrace ( " dl_sigma: " ++ (show dl_sigma)) $
  mtrace ( " alnew: " ++ (show al)) $
--   mtrace ( " k: " ++ (show k)) $
  let rhos = filter_dl_al nogood assig al in
  mtrace ( "rhos: " ++ (show rhos) ++ " sigma: " ++ (show sigma)) $
  if only rhos sigma
  then (nogood, sigma, k)
  else
    let
      eps = get_epsilon nogoods sigma prefix
      reduced_eps = clauseWithoutSL eps (invert sigma)
      newnogood = joinClause reduced_nogood reduced_eps
    in
    trace ( ">>> ca: reeps: "++ (show reduced_eps) ++ "redel: "++ (show reduced_nogood)  ++ "newnogood: "++ (show newnogood)) $
    conflict_analysis alt nogoods newnogood prefix (i+1)



get_epsilon:: [Clause] -> SignedVar -> Assignment -> Clause

-- get_epsilon [] l prefix = ([],[]) -- error ?
get_epsilon [] l prefix =  error "no antecedent epsilon found"

get_epsilon (ng:ngs) sigma prefix =
  let temp = clauseWithoutSL ng (invert sigma) in
  mtrace ( "geteps: " ++ (show (sigma)) ++ (show ng) ++ (show temp) ++ (show prefix)
  ++ " isincl: " ++ (show (is_included temp prefix))) $
  if is_included temp prefix
  then ng
  else (get_epsilon ngs sigma prefix)



-- -----------------------------------------------------------------------------

-- Propagation

data PropRes =  ASSIGNMENT Assignment  -- result of propagation can either be a conflict or a new assignment
         | Conflict Clause Assignment
         deriving (Show,Eq)


ng_prop::  [Rule] -> Int -> [Clause] -> [Clause] -> Assignment -> [SPVar] -> [Atom] -> (PropRes,[Clause],Int)
ng_prop prg al ngs_p ngs assig spvars u =
  let
    spc = initspc prg
    nogoods= ngs_p++ngs
    (maybeassig,al2) = (local_propagation prg al (cycle nogoods) 0 (length nogoods) assig)
  in
  case maybeassig of                                                            -- TODO if prg is tight skip unfounded set check
    ASSIGNMENT assig2 ->
--        mtrace ( "unfound set check: "
--          ++ (show u)
--        ) $
       let u2 = u \\ (falseatoms assig2 spvars) in   -- non false atoms
--        mtrace ("unfounded set check") $
                            if null u2
                            then                                                -- unfounded set check
                              let u3 = (unfounded_set prg spc assig2 spvars) in
                              if null u3
                              then (ASSIGNMENT assig2, ngs,al2)
                              else                                              -- learn loop nogood
                                let
                                    p = get_svar ((ALit (head u3))) spvars
                                in
--                                 mtrace ("ufs found: "++(show u3)) $
                                if elemAss (T p) assig2
                                then
                                  let cngs_of_loop = (loop_nogoods prg u3)
                                      ngs_of_loop = transforms cngs_of_loop spvars
                                  in

                                  (ASSIGNMENT assig2,(ngs_of_loop++ngs),al2)
                                else
                                  let
                                    assig3 = assign assig2 (F p) al2             -- extend assignment
                                  in
                                  case elemAss (F p) assig2 of
                                    True  -> ng_prop prg al2 ngs_p ngs assig2 spvars u3
                                    False -> ng_prop prg al2 ngs_p ngs assig3 spvars u3
                            else                                                -- learn loop nogood from u2
                              let
                                  p = get_svar ((ALit (head u2))) spvars
                                  cngs_of_loop = (loop_nogoods prg u2)
                                  ngs2 = (transforms cngs_of_loop spvars) ++ngs
                              in
                              if elemAss (T p) assig2
                              then (ASSIGNMENT assig2, ngs2,al2)
                              else
                                let
                                  assig3 = assign assig2 (F p) al2              -- extend assignment
                                in
                                if (elemAss (F p) assig2)
                                then
                                  ng_prop prg al2 ngs_p ngs2 assig2 spvars u2
                                else
                                  ng_prop prg al2 ngs_p ngs2 assig3 spvars u2

    Conflict ccl cass -> (Conflict ccl cass, ngs,al2)                               -- return conflic clause



local_propagation::  [Rule] -> Int -> [Clause] -> Int -> Int -> Assignment -> (PropRes,Int)
-- takes a program a cyclic list of nogoods and an assignment and returns a propagation result
local_propagation p al (ng:nogoods) done todo assig =
  let up = unitresult al assig ng  in
--   trace ("al: " ++ (show al)) $
  case up of
    Nix           -> if (done+1) == todo
                     then (ASSIGNMENT assig,al)
                     else (local_propagation p al nogoods (done+1) todo assig)
    ASSI newassig ->
      trace ("al: " ++ (show al)) $
      local_propagation p (al+1) nogoods 0 todo newassig         -- increase assignment level
    Conf ccl -> (Conflict ccl assig,al)                                         -- return conflict clause


data Res = ASSI Assignment  -- result of propagation can either be a conflict or a new assignment
         | Conf Clause
         | Nix
         deriving (Show,Eq)

unitresult:: Int -> Assignment -> Clause -> Res
unitresult dl assig nogood =
  case (resolve nogood assig) of
    CONF  ->     mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig) ++ " = conflict") $
                 Conf nogood
    Res (T l) -> if isassigned l assig
                 then
--                    mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig)) $
                   Nix
                 else
                   mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig) ++ " = " ++ (show (T l))) $
                   ASSI (assign assig (T l) dl)
    Res (F l) -> if isassigned l assig
                 then
--                    mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig)) $
                   Nix
                 else
                   mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig) ++ " = " ++ (show (F l))) $
                   ASSI (assign assig (F l) dl)
    NIX       -> {-mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig)) $-}
                 Nix                                                            -- nothing can be derived
