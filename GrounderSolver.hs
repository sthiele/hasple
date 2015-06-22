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
  show_as, print_as,
  gr_solve,
)where

import Grounder
import Solver
import LPParser -- for parsing in tests
import ASP
import Data.List (sort, nub, intersect, (\\), delete )
import Data.Maybe

assi:: [Rule] -> [[Atom]]
-- assi x = anssets x
assi x = cdnl_enum x 0

show_lp:: [Rule] -> [Char]
show_lp [] = ""
show_lp (x:xs) = (show x) ++ "\n" ++ (show_lp xs)

show_as:: [[Atom]] -> [Char]
show_as [] = "No Answersets"
show_as (x:xs) = (show_as2 (x:xs) 1)

print_as [] = putStr "No Answersets"
print_as (x:xs) = print_as2 1 (x:xs)

show_as2:: [[Atom]] -> Int -> [Char]
show_as2 [] n = ""
show_as2 (x:xs) n = "Answer " ++ (show n) ++ ":\n" ++ show_as3 x ++"\n"++ (show_as2 xs (n+1))

print_as2 n [] = print ""
print_as2 n (x:xs)  = do
    putStr "Answer "
    print n
    print_as3 x
    print_as2 (n+1) xs

show_as3:: [Atom] -> [Char]
show_as3 [] = ""
show_as3 (x:xs) =  (show x) ++ " " ++ (show_as3 xs)

print_as3 [] = putStr "\n"
print_as3 (x:xs) =
    do
        putStr (show x)
        putStr " "
        print_as3 xs

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


-- gr_solve, returns the answer sets of a program
gr_solve:: [Rule] -> [[Atom]]
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

-- -------------------------------------
-- Tests
-- -------------------------------------

test_old:: [Char] -> String
test_old x =
  do
    case readProgram x of
      Left  err -> "ParseError: " ++ (show err)
      Right prg ->
--                      "Program found:\n" ++
--                      show_lp prg ++
                   show_as (sort (map sort (assi (groundProgram prg))))


test_new:: [Char] -> String
test_new x =
  do
    case readProgram x of
      Left  err -> "ParseError: " ++ (show err)
      Right prg -> show_as (sort (map sort (gr_solve prg)))

test:: [Char] -> IO()
test x =
  do
    case readProgram x of
      Left  err -> print $ "ParseError: " ++ (show err)
      Right prg -> putStrLn $ show_as (gr_solve prg)


test_good:: [Char] -> String
test_good x =
  do
    case readProgram x of
      Left  err -> "ParseError: " ++ (show err)
      Right prg -> show_as (sort (map sort (anssets (groundProgram prg))))

-- ground_facts     = "f(a).\n"
--                 ++ "f(b).\n"
--                 ++ "f(c).\n"
-- --                 ++ "r(b).\n"
-- nonground_facts  = "x(X).\n"
-- --                 ++ "r(Y).\n"
-- ground_rules     = "f(b) :- f(a). \n"
-- --                 ++ "a(a1) :- q(a). \n"
-- --                 ++ "a(b1) :- q(b). \n"
--
-- nonground_rules  = "y(X) :- x(X). \n"
--                 ++ "q(X) :- f(X), not p(X), not r(X). \n"
--                 ++ "p(X) :- f(X), not q(X), not r(X). \n"
--                 ++ "r(X) :- f(X), not p(X), not q(X). \n"
--                 ++ "q2(X) :- f(X), not p2(X), not r2(X). \n"
--                 ++ "p2(X) :- f(X), not q2(X), not r2(X), not a(a1). \n"
--                 ++ "r2(X) :- f(X), not p2(X), not q2(X). \n"
--
-- ground_ics       = ":- r(a).\n"
--                 ++ ":- a(a1),a(b1).\n"
-- nonground_ics    = ":- r(X)."
--
-- myprg1 = ground_facts ++ nonground_facts ++ ground_rules ++ nonground_rules ++ ground_ics ++ nonground_ics
--
-- myprg2 = myprg1++"r(b).\n"



mpr1 = "a :- not b, not c.\n"
    ++ "b :- not a, not c.\n"
    ++ "c :- not a, not b.\n"
Right mp1 = readProgram mpr1

mpr2 = " a :- not b.\n"
Right mp2 = readProgram mpr2

mpr3 = "q(a) :- not p(a).\n"
    ++ "q(b) :- not p(b).\n"
    ++ "p(a) :- not q(a).\n"
    ++ "p(b) :- not q(b).\n"
Right mp3 = readProgram mpr3

mpr4 = "a:-b.\n"
    ++ "b:-a.\n"
Right mp4 = readProgram mpr4

mpr5 = "a :- b.\n"
    ++ "b :- not a.\n"
Right mp5 = readProgram mpr5

mpr6 = "a :- b.\n"
     ++ "b :- not a.\n"
     ++ "b :- x.\n"
     ++ "x :- not y.\n"
     ++ "y :- not x.\n"
Right mp6 = readProgram mpr6

mpr6a = "v :- u,y.\n"   -- example from Conflict-Driven Answer Set Solving p4
     ++ "u :- v.\n"
     ++ "u :- x.\n"
     ++ "x :- not y.\n"
     ++ "y :- not x.\n"
Right mp6a = readProgram mpr6a

mpr6b = "v :- u.\n"
     ++ "u :- v.\n"
     ++ "u :- x.\n"
     ++ "x :- not y.\n"
     ++ "y :- not x.\n"
Right mp6b = readProgram mpr6b

mpr7 = "a :- b.\n"
    ++ "b :- c.\n"
    ++ "c :- not a.\n"
    ++ "c :- x.\n"
    ++ "x :- not y.\n"
    ++ "y :- not x.\n"
Right mp7 = readProgram mpr7

mpr8 = "f(a).\n"
    ++ "f(b).\n"
    ++ "f(c).\n"
    ++ "q(X):- f(X), not p(X). \n"
    ++ "p(X) :-f(X), not q(X). \n"
Right mp8 = readProgram mpr8

mpr9 = "f(a).\n"
    ++ "f(b).\n"
    ++ "f(c).\n"
    ++ "f(d).\n"
    ++ "f(e).\n"
    ++ "f(f).\n"
    ++ "f(g).\n"
    ++ "f(h).\n"
    ++ "q(X):- f(X), not p(X), not r(X).\n"
    ++ "p(X) :-f(X), not q(X), not r(X).\n"
    ++ "r(X) :-f(X), not p(X), not q(X).\n"
    ++ ":- r(X).\n"
Right mp9 = readProgram mpr9

mpr10 = ":- r(X).\n"
Right mp10 = readProgram mpr10

mpr11 = "a.\n"
     ++ "b :- not a.\n"
     ++ "c :- a, not d.\n"
     ++ "d :- not c, not e.\n"
     ++ "e :- b.\n"
     ++ "e :- e.\n"
Right mp11 = readProgram mpr11

mpr12 = "a :- not b.\n"
     ++ "b :- not a.\n"
     ++ "c :- a.\n"
     ++ "c :- b, d.\n"
     ++ "d :- b, c.\n"
     ++ "d :- e.\n"
     ++ "e :- b, not a.\n"
     ++ "e :- c, d.\n"
Right mp12 = readProgram mpr12

mpr13 = "f(c).\n"
     ++ "q :- f(X), not p, not r.\n"
     ++ "p :-f(X), not q, not r\n."
     ++ "r :-f(X), not p, not q.\n"
     ++ ":- r.\n"
     ++ "p :- f(X), not q, not r.\n"
     ++ "f:-q.\n"



unit_test =
  (test_new mpr1)==(test_good mpr1) &&
  (test_new mpr2)==(test_good mpr2) &&
  (test_new mpr3)==(test_good mpr3) &&
  (test_new mpr4)==(test_good mpr4) &&
  (test_new mpr5)==(test_good mpr5) &&
  (test_new mpr6)==(test_good mpr6) &&
  (test_new mpr6a)==(test_good mpr6a) &&
  (test_new mpr6b)==(test_good mpr6b) &&
  (test_new mpr7)==(test_good mpr7) &&  -- infinite
--   (test_new mpr8)==(test_good mpr8) &&  -- test takes too long
--   (test_new mpr9)==(test_good mpr9) &&  -- test takes too long
  (test_new mpr10)==(test_good mpr10) &&
  (test_new mpr11)==(test_good mpr11) &&
  (test_new mpr12)==(test_good mpr12) &&
  (test_new mpr13)==(test_good mpr13)



