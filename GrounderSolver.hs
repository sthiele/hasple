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

module GrounderSolver (
  gr_solve,
)where

import Grounder
-- import GoodSolver
import CDNLSolver
import ASP
import Data.List (sort, nub, intersect, (\\), delete )
import Data.Maybe

assi:: [Rule] -> [[Atom]]
-- function used to compute answer sets
-- assi x = anssets x
assi x = cdnl_enum x 0


get_ics:: [Rule] -> [Rule]
-- returns the integrity constraints of a program
get_ics [] = []
get_ics ((Rule h b):rs) =
  if (h == __conflict)
  then ((Rule h b): get_ics rs)
  else get_ics rs


simplifyProgramm:: [Rule] -> ([Atom],[Atom]) -> [Rule]
-- does remove facts
simplifyProgramm [] (t,f) = []
simplifyProgramm x (t,f) = (mapMaybe (simplifyRule (t,f)) x)


simplifyRule:: ([Atom],[Atom]) -> Rule -> Maybe Rule
simplifyRule (t,f) (Rule h b) =
  let nb = nbody (Rule h b)
      pb = pbody (Rule h b)
  in
  if ( (elem h t) || not (null (intersect nb t)) || not (null (intersect pb f)))
  then Nothing
  else
  let newpbody = (nub pb) \\ t
      newnbody = (nub nb) \\ f
  in
  Just (normalRule h newpbody newnbody)


groundProgramx:: [Rule] -> AtomMap -> [Rule]
groundProgramx p am =
  let am2 = insert_atoms am (heads_p  p)
      pg1 = nub (concatMap  (groundRule am2)  p)
  in
  if pg1==p
  then pg1
  else groundProgram pg1


get_query_rules:: [Rule] -> Atom -> [Rule]
get_query_rules rules a = get_query_rulesx rules [] [] a

get_query_rulesx:: [Rule] -> [Rule] -> [Atom] -> Atom -> [Rule]
get_query_rulesx rules acc found a =
  let grules = get_query_rules2 rules a
      nacc = grules++acc
      next = nub (concatMap pbody grules) ++ (concatMap nbody grules)
      nn = next \\ (a:found)
  in
  if nn==[]
  then nub nacc
  else concatMap (get_query_rulesx rules nacc (a:found)) nn



get_query_rules2:: [Rule] -> Atom -> [Rule]
get_query_rules2 [] _ = []

get_query_rules2 (r:rs) a =
  case matchAtom (kopf r) a of
    Just binding -> let gr = applySubs binding r
                        grs = get_query_rules2 rs a
                    in
                    nub (gr: grs)
    Nothing ->      get_query_rules2 rs a

-- ------------------------------------------------------------


gr_solve:: [Rule] -> [[Atom]]
-- gr_solve, returns the answer sets of a program
gr_solve prg =  gr_solve_l (prg,[],[])

-- returns the answer sets of a program that are consistent with the answer candidate
gr_solve_l:: ([Rule],[Atom],[Atom]) -> [[Atom]]
gr_solve_l (prg, cons, falses) =
  let
    mos = insert_atoms emptyAtomMap cons
    ics = get_ics prg
    gr_ics = simplifyProgramm (nub (concatMap (groundRule mos) ics)) (cons,falses)
    wfm = assi gr_ics
    choice_candidates = heads_p prg                                     -- TODO: make sure ground atoms are first
   in
   if ( wfm == [])
   then []
   else
     if (choice_candidates==[])
     then [cons]
     else
       let
         choice = head choice_candidates
         queries = get_query_rules prg choice
         gr_queries = (simplifyProgramm (groundProgramx (queries++ics) mos) (cons,falses))
         eval_atoms = nub (atoms_p gr_queries)
         tas = (assi (gr_queries))
         nfalses = map (nt falses eval_atoms) tas
         ncons = map (cons ++) tas  --as candidates
         mixed = zip ncons nfalses
         rest_prg = prg \\ queries
         nsimplified_prg =  map (simplifyProgramm rest_prg) mixed
         list = zip3 nsimplified_prg ncons nfalses
       in
       concatMap gr_solve_l list


nt:: [Atom] -> [Atom] -> [Atom] -> [Atom]
nt old a t = old ++ (a \\ t)



