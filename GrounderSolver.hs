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
  show_as,
--   show_as3,
  gr_solve,
)where

import Grounder
import Solver
import LPParser -- for tests
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

show_as2:: [[Atom]] -> Integer -> [Char]
show_as2 [] n = ""
show_as2 (x:xs) n = "Answer " ++ (show n) ++ ":\n" ++ show_as3 x ++"\n"++ (show_as2 xs (n+1))

show_as3:: [Atom] -> [Char]
show_as3 [] = ""
show_as3 (x:xs) =  (show x) ++ " " ++ (show_as3 xs)


-- returns the integrity constraints of a program
get_ics:: [Rule] -> [Rule]
get_ics [] = []
get_ics ((Rule h pb nb):rs) =
  if (h == __conflict)
  then ((Rule h pb nb): get_ics rs)
  else get_ics rs



simplifyProgramm:: [Rule] -> ([Atom],[Atom]) -> [Rule]
-- does remove facts
simplifyProgramm [] (t,f) = []
simplifyProgramm x (t,f) = (mapMaybe (simplifyRule (t,f)) x)

simplifyProgramm2:: [Rule] -> ([Atom],[Atom]) -> [Rule]
-- does not remove facts
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

consequences:: [Rule] -> [Atom] -> [Atom] -> ([Atom],[Atom])
-- return consequences of a programm
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

nfacts:: [Rule] -> [Atom]
-- return atoms of a programm that dont have a matching head
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
       Just binding ->  let gr = groundRule2 r binding
                            grs = get_query_rules2 rs a
                        in
                        nub (gr: grs)
       Nothing ->       get_query_rules2 rs a

-- get_query_rules2 [] _ = []
-- get_query_rules2 prg a =
--   let mymatchAtom x y = matchAtom y x
--       kopfe = map kopf prg
--       matches =  map mymatchAtom a kopfe
--
--   [ groundRule2 r binding | r <- prg, let (Just binding)=(matchAtom (kopf r) a) ]

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

         tas =  (assi (gr_queries))
         nfalses = map (nt falses eval_atoms) tas
         ncons = map (cons ++) tas  --as candidates
         mixed = zip ncons nfalses
         rest_prg = prg \\ queries
         nsimplified_prg =  map (simplifyProgramm rest_prg) mixed
         list = zip3 nsimplified_prg ncons nfalses
       in
       concatMap gr_solve_l list




intersectAll:: [[Atom]] -> [Atom]
intersectAll [] = []
intersectAll [x] = x
intersectAll (x:xs) = intersect x (intersectAll xs)


nt:: [Atom] -> [Atom] -> [Atom] -> [Atom]
nt old a t = old ++ (a \\ t)

-- -------------------------------------
-- Tests
-- -------------------------------------

test_old:: [Char] -> IO ()
test_old x =
    do
         case readProgram x of
           Left  err -> putStrLn ("ParseError: " ++ show err)
           Right val -> putStrLn (
--                         "Program found:\n" ++
--                         show_lp val ++
                        show_as  (assi (groundProgram val))
                        )

test_new:: [Char] -> IO ()
test_new x=
  do
    case readProgram x of
      Left  err -> putStrLn ("ParseError: " ++ show err)
      Right prg ->  putStrLn (show_as (gr_solve prg))


ground_facts     = "f(a).\n"
                ++ "f(b).\n"
                ++ "f(c).\n"
--                 ++ "r(b).\n"
nonground_facts  = "x(X).\n"
--                 ++ "r(Y).\n"
ground_rules     = "f(b) :- f(a). \n"
--                 ++ "a(a1) :- q(a). \n"
--                 ++ "a(b1) :- q(b). \n"

nonground_rules  = "y(X) :- x(X). \n"
                ++ "q(X) :- f(X), not p(X), not r(X). \n"
                ++ "p(X) :- f(X), not q(X), not r(X). \n"
                ++ "r(X) :- f(X), not p(X), not q(X). \n"
                ++ "q2(X) :- f(X), not p2(X), not r2(X). \n"
                ++ "p2(X) :- f(X), not q2(X), not r2(X), not a(a1). \n"
                ++ "r2(X) :- f(X), not p2(X), not q2(X). \n"

ground_ics       = ":- r(a).\n"
                ++ ":- a(a1),a(b1).\n"
nonground_ics    = ":- r(X)."

myprg1 = ground_facts ++ nonground_facts ++ ground_rules ++ nonground_rules ++ ground_ics ++ nonground_ics

myprg2 = myprg1++"r(b).\n"


mpr1a = " a :- not b.\n"
Right mp1a = readProgram mpr1a

mpr1 = "a :- not b, not c.\n"
    ++ "b :- not a, not c.\n"
    ++ "c :- not a, not b.\n"
Right mp1 = readProgram mpr1

mpr1b = "q(a) :- not p(a).\n"
     ++ "q(b) :- not p(b).\n"
     ++ "p(a) :- not q(a).\n"
     ++ "p(b) :- not q(b).\n"
Right mp1b = readProgram mpr1b

mpr2 = "a:-b.\n"
    ++ "b:-a.\n"
Right mp2 = readProgram mpr2

mpr2b = "a :- b.\n"
     ++ "b :- not a.\n"
Right mp2b = readProgram mpr2b

mpr3 = "f(a).\n"
    ++ "f(b).\n"
    ++ "f(c).\n"
    ++ "f(d).\n"
    ++ "f(e).\n"
    ++ "f(f).\n"
    ++ "q(X):- f(X), not p(X). \n"
    ++ "p(X) :-f(X), not q(X). \n"
Right mp3 = readProgram mpr3

mpr4 = "f(a).\n"
    ++ "f(b).\n"
    ++ "q(X):- f(X), not p(X), not r(X).\n"
    ++ "p(X) :-f(X), not q(X), not r(X).\n"
    ++ "r(X) :-f(X), not p(X), not q(X).\n"
    ++ ":- r(X).\n"
Right mp4 = readProgram mpr4

mpr5 = ":- r(X).\n"
Right mp5 = readProgram mpr5

mpr6 = "a.\n"
    ++ "b :- not a.\n"
    ++ "c :- a, not d.\n"
    ++ "d :- not c, not e.\n"
    ++ "e :- b.\n"
    ++ "e :- e.\n"
Right mp6 = readProgram mpr6

mpr7 = "a :- not b.\n"
    ++ "b :- not a.\n"
    ++ "c :- a.\n"
    ++ "c :- b, d.\n"
    ++ "d :- b, c.\n"
    ++ "d :- e.\n"
    ++ "e :- b, not a.\n"
    ++ "e :- c, d.\n"
Right mp7 = readProgram mpr7

mpr8 = "f(c).\n"
    ++ "q :- f(X), not p, not r.\n"
    ++ "p :-f(X), not q, not r\n."
    ++ "r :-f(X), not p, not q.\n"
    ++ ":- r.\n"
    ++ "p :- f(X), not q, not r.\n"
    ++ "f:-q.\n"







