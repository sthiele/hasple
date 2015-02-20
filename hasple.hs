-- Copyright (c) 2014, Sven Thiele <sthiele78@gmail.com>

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

import Data.List (nub,(\\))

show_lp [] = ""
show_lp (x:xs) = (show x) ++ "\n" ++ (show_lp xs)

show_as [] = "No Answersets"
show_as (x:xs) = (show_as2 (x:xs) 1)

show_as2 [] n = ""
show_as2 (x:xs) n = "\nAnswer " ++ (show n) ++ ":\n" ++ (show_as3 x) ++ "\n" ++ (show_as2 xs (n+1))

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
           Right val -> putStrLn ("Program found:\n" ++
                        (show_lp val) ++
                        show_as (sol (findas (groundProgram val) 0)))


test_old x =
    do
         case readProgram x of
           Left  err -> putStrLn ("ParseError: " ++ show err)
           Right val -> putStrLn ("Program found:\n" ++
                        (show_lp val) ++
                        show_as (sol (findas (groundProgram val) 0)))

      

mix:: [[Rule]] -> [[Atom]] -> [([Rule],[Atom])]
mix [] _ = []
mix _ [] = []
mix (x:xs) (y:ys) = ((x,y):(mix xs ys))                        
                        
--outerloop, returns the answer sets of a program                        
loop prg =
                   let
                     cons = consequences prg
                     mos = getpredval cons
                     ics = get_ics prg
                     gr_ics = simplifyProgramm (nub (concatMap (groundRule mos) ics)) cons
                     wfm = findas gr_ics 1
                     simplified_prg = (simplifyProgramm prg cons)
--                      (ground_simpl, nonground_simpl) = bla simplified_prg
--                      ground_choice_candidates = heads_p ground_simpl
--                      nongrnd_choice_candidates = heads_p nonground_simpl
                     choice_candidates = heads_p simplified_prg -- make sure ground atoms are first
                    in
                    if ( sol wfm == [])                   
                    then []
                    else
                      if (choice_candidates==[])
                      then [cons]                      
                      else
                        let
                          choice = head choice_candidates
                          queries = get_query_rules simplified_prg choice
                          gr_queries = simplifyProgramm (nub (concatMap (groundRule mos) (queries++ics))) cons
                          tas = sol (findas gr_queries 0)
                          ncons = map (cons ++) tas --as candidates
                          nmos = map (getpredval) ncons                          
                          temp_prg = simplified_prg \\ queries
                          nsimplified_prg =  map (simplifyProgramm temp_prg) ncons
                          list = mix nsimplified_prg ncons
                        in
                        concatMap inner list
                        

                        
-- returns the answer sets consistent with the subsequent components
inner:: ([Rule],[Atom]) -> [[Atom]]
inner (prg, cons) =
                   let
                     mos = getpredval cons
                     ics = get_ics prg
                     gr_ics = simplifyProgramm (nub (concatMap (groundRule mos) ics)) cons
                     wfm = findas gr_ics 1
--                      (ground_simpl, nonground_simpl) = bla prg
--                      ground_choice_candidates = heads_p ground_simpl
--                      nongrnd_choice_candidates = heads_p nonground_simpl
                     choice_candidates = heads_p prg
                    in
                    if ( sol wfm == [])                   
                    then []
                    else
                      if (choice_candidates==[])
                      then [cons]                      
                      else
                        let
                          choice = head choice_candidates
                          queries = get_query_rules prg choice
                          gr_queries = simplifyProgramm (nub (concatMap (groundRule mos) (queries++ics))) cons
                          tas = sol (findas gr_queries 0)
                          ncons = map (cons ++) tas --as candidates
                          nmos = map (getpredval) ncons
                          temp_prg = prg \\ queries
                          nsimplified_prg =  map (simplifyProgramm temp_prg) ncons
                          list = mix nsimplified_prg ncons
                        in
                        concatMap inner list                        

test_new :: [Char] -> IO ()
test_new x= 
  do
    case readProgram x of
      Left  err -> putStrLn ("ParseError: " ++ show err)
      Right prg ->  putStrLn (show_as (loop prg))


                        
                        
test_verb :: [Char] -> IO ()
test_verb x =
  do
    case readProgram x of
      Left  err -> putStrLn ("ParseError: " ++ show err)
      Right prg -> 
                   let
                     (ground, nonground) = bla prg
                     cons = consequences prg
                     mos = getpredval cons
                     ics = get_ics prg
                     gr_ics = simplifyProgramm (nub (concatMap (groundRule mos) ics)) cons
                     wfm = findas gr_ics 1
                     simplified_prg = (simplifyProgramm prg cons)
                     (ground_simpl, nonground_simpl) = bla simplified_prg
                     ground_choice_candidates = heads_p ground_simpl
                     nongrnd_choice_candidates = heads_p nonground_simpl
                     choice_candidates = heads_p simplified_prg
                    in
                    if ( sol wfm == [])                   
                    then putStrLn ("Program found:\n" ++ (show_lp prg)
                      ++ "\nGround rules:\n"
                      ++ show_lp ground
                      ++ "\nNonGround rules:\n"  
                      ++ show_lp nonground               
                      ++"\nNo Solution."
                      ++ "\n")
                    else
                      if (choice_candidates==[])
                      then
                        putStrLn ("Program found:\n" ++ (show_lp prg)
                        ++ "\nGround rules:\n"
                        ++ show_lp ground
                        ++ "\nNonGround rules:\n"
                        ++ show_lp nonground
                        ++ "\nConsequences:\n"
                        ++ show cons ++"\n"
                        ++ "\nNo Choice left"
                        ++ "\n")
                      else
                        let
                          choice = head choice_candidates
                          queries = get_query_rules simplified_prg choice
                          gr_queries = simplifyProgramm (nub (concatMap (groundRule mos) (queries++ics))) cons
                          tas = sol (findas gr_queries 0)
                          mas = map (cons ++) tas --ncons
                          nmos = map (getpredval) mas
                          temp_prg = simplified_prg \\ queries
                          nsimplified_prg =  map (simplifyProgramm temp_prg) mas
                          example = head nsimplified_prg
                          nchoice_candidates = map heads_p nsimplified_prg
                        in
                        putStrLn ("Program found:\n" ++ (show_lp prg)
                        ++ "\nGround rules:\n"
                        ++ show_lp ground
                        ++ "\nNonGround rules:\n"
                        ++ show_lp nonground
                        ++ "\nConsequences:\n"
                        ++ show cons ++"\n"
                        ++ "\nChoice Candidates:\n"
                        ++ show ground_choice_candidates ++"\n"
                        ++ show nongrnd_choice_candidates ++ "\n"
                        ++ "\nSimplifiedProgram :\n"
                        ++ "\nGround rules:\n"
                        ++ (show_lp ground_simpl)
                        ++ "\nNonGround rules:\n"
                        ++ (show_lp nonground_simpl)
                        ++ "\nChoice:" ++ show choice
                        ++ "\nChoosenRules:" ++ show_lp queries
                        ++ "\nChoosenGRules simplified:\n" ++ show_lp gr_queries
                        ++ "\nAnswerSet:" ++ show_as mas
                        ++ "example simplified prg"++ show_lp example
                        ++ "\n")

                        

ground_facts     = "f(a).\n"
                ++ "f(b).\n"
                ++ "f(c).\n"
--                 ++ "r(b).\n" 
nonground_facts  = "x(X).\n"
--                 ++ "r(Y).\n"
ground_rules     = "f(b) :- f(a). \n" 
                ++ "a(a1) :- q(a). \n"
                ++ "a(b1) :- q(b). \n"

nonground_rules  = "y(X) :- x(X). \n"
                ++ "q(X) :- f(X), not p(X), not r(X). \n"
                ++ "p(X) :- f(X), not q(X), not r(X). \n"
                ++ "r(X) :- f(X), not p(X), not q(X). \n"
                     
ground_ics       = ":- r(a).\n"
                ++ ":- a(a1),a(b1).\n"
nonground_ics    = ":- r(X)."

myprg1 = ground_facts ++ nonground_facts ++ ground_rules ++ nonground_rules ++ ground_ics ++ nonground_ics

myprg2 = myprg1++"r(b).\n"

myprg3 = "f(a).\n"
      ++ "q(X) :- f(X), not p(X). \n"
      ++ "p(X) :- f(X), not q(X). \n"
      ++ "q1(X) :- f(X), not p1(X). \n"
      ++ "p1(X) :- f(X), not q1(X). \n"
      
      