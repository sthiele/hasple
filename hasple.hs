-- Copyright (c) 2015, Sven Thiele <sthiele78@gmail.com>

-- This file is part of hasple.

-- hasple is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.

-- hasple is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.

-- You should have received a copy of the GNU General Public License
-- along with hasple.  If not, see <http://www.gnu.org/licenses/>.

import System.Environment
import ASP
import LPParser
import Solver

import Data.List (nub,(\\), intersect, sort)

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



main :: IO ()  
main =
  do
    args <- getArgs
    if args==[]
       then putStrLn "No arguments given!"
       else do
         putStrLn ("Answer Set Solver in Haskell by Sven Thiele 2014.\n")
         contents <- readFile (head args)
         case readProgram contents of
           Left  err -> putStrLn ("ParseError: " ++ show err)
           Right val -> putStrLn $ "Program found:"
                        ++ show_lp val
--                         ++ show_as (sol (findas (groundProgram val) 0)))
                        ++ show_as (outer val)
                        

test_old x =
    do
         case readProgram x of
           Left  err -> putStrLn ("ParseError: " ++ show err)
           Right val -> putStrLn ("Program found:\n" ++
                        show_lp val 
                        ++ show_as  (assi (groundProgram val))
                        )
      

mix:: [[Atom]] -> [[Atom]] -> [([Atom],[Atom])]
mix [] _ = []
mix _ [] = []
mix (x:xs) (y:ys) = ((x,y):(mix xs ys))

mix3:: [[Rule]] -> [[Atom]] -> [[Atom]] -> [([Rule],[Atom],[Atom])]
mix3 [] _ _ = []
mix3 _ [] _ = []
mix3 _ _ [] = []
mix3 (x:xs) (y:ys) (z:zs)= ((x,y,z):(mix3 xs ys zs))
                        
-- outer, returns the answer sets of a program
outer prg =
                   let
                     (cons,falses) = consequences prg [] []
                     mos = getpredval cons
                     ics = get_ics prg
                     gr_ics = simplifyProgramm (nub (concatMap (groundRule mos) ics)) (cons,falses)
                     wfm = assi gr_ics
                     simplified_prg = simplifyProgramm prg (cons,falses)
                     choice_candidates = heads_p simplified_prg -- make sure ground atoms are first
                    in
                    if ( wfm == [])
                    then []
                    else
                      if (choice_candidates==[])
                      then [cons]                      
                      else
                        let
                          choice = head choice_candidates
                          queries = get_query_rules simplified_prg choice
                          gr_queries = (simplifyProgramm (groundProgramx (queries++ics) mos) (cons,falses))
                          eval_atoms = nub (atoms_p gr_queries)
                          
                          tas =  (assi (gr_queries))
                          nfalses = map (nt falses eval_atoms) tas
                          ncons = map (cons ++) tas --as candidates
                          rest_prg = simplified_prg \\ queries

                          mixed = mix ncons nfalses
                          nsimplified_prg =  map (simplifyProgramm rest_prg) mixed
                          list = mix3 nsimplified_prg ncons nfalses
                        in
                        concatMap inner list


                            
                        
-- returns the answer sets of a program that are consistent with the answer candidate
inner:: ([Rule],[Atom],[Atom]) -> [[Atom]]
inner (prg, cons, falses) =
                   let
                     mos = getpredval cons
                     ics = get_ics prg
                     gr_ics = simplifyProgramm (nub (concatMap (groundRule mos) ics)) (cons,falses)
                     wfm = assi gr_ics
                     choice_candidates = heads_p prg
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
                          mixed = mix ncons nfalses
                          rest_prg = prg \\ queries
                          nsimplified_prg =  map (simplifyProgramm rest_prg) mixed
                          list = mix3 nsimplified_prg ncons nfalses
                        in
                        concatMap inner list                        


-- findas prg = let (answers, nogoods) = findas2 prg [] [] [] []
--              in answers



 
 
  
                        
test_new :: [Char] -> IO ()
test_new x=
  do
    case readProgram x of
      Left  err -> putStrLn ("ParseError: " ++ show err)
      Right prg ->  putStrLn (show_as (outer prg))


                        
                        
test_verb :: [Char] -> IO ()
test_verb x =
  do
    case readProgram x of
      Left  err -> putStrLn ("ParseError: " ++ show err)
      Right prg -> 
                   let
                     (cons,falses) = consequences prg [] []
                     mos = getpredval cons
                     ics = get_ics prg
                     gr_ics = simplifyProgramm (nub (concatMap (groundRule mos) ics)) (cons,falses)
--                      wfm = anssets gr_ics
                     wfm = assi gr_ics
                     simplified_prg = (simplifyProgramm prg (cons,falses))
                     choice_candidates = heads_p simplified_prg
                    in
                    if (wfm == [])
                    then putStrLn ("Program found:\n" ++ (show_lp prg)
                      ++"\nNo Solution."
                      ++ "\n")
                    else
                      if (choice_candidates==[])
                      then
                        putStrLn ("Program found:\n" ++ (show_lp prg)
                        ++ "\nPosConsequences:\n"
                        ++ show cons ++"\n"
                        ++ "\nNegConsequences:\n"
                        ++ show falses ++"\n"
                        ++ "\nNo Choice left"
                        ++ "\n")
                      else
                        let
                          choice = head choice_candidates
                          queries = get_query_rules simplified_prg choice
                          gr_queries = (simplifyProgramm (groundProgramx (queries++ics) mos) (cons,falses))
                          eval_atoms = nub (atoms_p gr_queries)
                          tas =  assi (gr_queries)
                          
--                           intersectionas =  intersectAll tas
                          ncons = map (cons ++) tas
                          intersectionncons =  intersectAll ncons
                          nfalses = map (nt falses eval_atoms) tas
                          intersectionnfalses = intersectAll nfalses
                          mixed = mix ncons nfalses
--                           mixedintersection = (intersectionncons, intersectionnfalses)
--                           rest_prg = simplifyProgramm (simplified_prg \\ queries) mixedintersection
                          rest_prg = simplified_prg \\ queries
                          nsimplified_prg =   map (simplifyProgramm rest_prg) mixed
                          example = head nsimplified_prg                         
                          list = mix3 nsimplified_prg ncons nfalses
                        in
                        putStrLn ("Program found:\n" ++ (show_lp prg)

                        ++ "\nPosConsequences:\n"
                        ++ show cons ++"\n"
                        ++ "\nNegConsequences:\n"
                        ++ show falses ++"\n"
                        ++ "\nSimplifiedProgram :\n"
                        ++ show_lp simplified_prg
                        ++ "\nChoice Candidates:\n" ++ show choice_candidates ++ "\n"
                        ++ "\nChoice:\n"  ++ show choice ++ "\n"
                        ++ "\nChoosenRules:\n" ++ show_lp (queries++ics)
                        ++ "\nChoosenGRules simplified:\n" ++ show_lp gr_queries
                        
                        ++ "\nRestProgram :\n"
                        ++ (show_lp rest_prg)
                        ++ "\nevaluated atoms:\n" ++ show eval_atoms
                        ++ "\nProposed AnswerSet extensions:\n" ++ show_as tas
--                         ++ "\nProposed AntiAnswerSet extensions:\n" ++ show_as nfalses
                        ++ "\nFinal AnswerSet:\n" ++ show_as ncons
                        ++ "\nexample simplified prg\n"++ show_lp example
--                         ++ "\ninner as\n"++ show_as (concatMap inner list)
                        ++ "\n")

intersectAll:: [[Atom]] -> [Atom]
intersectAll [] = []
intersectAll [x] = x
-- intersectAll [x,x2] = intersect x x2
intersectAll (x:xs) = intersect x (intersectAll xs)

                        
nt:: [Atom] -> [Atom] -> [Atom] -> [Atom]
nt old a t = old ++ (a \\ t)


assi = anssets


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

mpr4 =
  "f(a).\n"
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
    