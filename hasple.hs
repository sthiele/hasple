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
--                         "\nGrounded program:\n" ++
--                         show_lp (ground_program val) ++
                        show_as (sol (findas (groundProgram val) 0)))


test2 x =
    do
         case readProgram x of
           Left  err -> putStrLn ("ParseError: " ++ show err)
           Right val -> putStrLn ("Program found:\n" ++
                        (show_lp val) ++
--                         "\nGrounded program:\n" ++
--                         show_lp (ground_program val) ++
                        show_as (sol (findas (groundProgram val) 0)))

ground_facts     = "f(a).\n"
nonground_facts  = "x(X).\n"

ground_rules     = "f(b) :- f(a). \n" 
                ++ "a(b) :- q(a). \n"

nonground_rules  = "y(X) :- x(X). \n"
                ++ "q(X) :- f(X), not p(X), not r(X). \n"
                ++ "p(X) :- f(X), not q(X), not r(X). \n"
                ++ "r(X) :- f(X), not p(X), not q(X). \n"
                     
ground_ics       = ":- r(a).\n"
nonground_ics    = ":- r(X)."

myprg1 = ground_facts ++ nonground_facts ++ ground_rules ++ nonground_rules ++ ground_ics ++ nonground_ics


test :: [Char] -> IO ()
test x =
  do
    case readProgram x of
      Left  err -> putStrLn ("ParseError: " ++ show err)
      Right prg -> 
                   let
                     (ground, nonground) = bla prg
                     cons = consequences prg
                     simplified_prg = (simplifyProgramm prg cons)
                     (ground_simpl, nonground_simpl) = bla simplified_prg
                     ground_choice_candidates = heads_p ground_simpl
                     nongrnd_choice_candidates = heads_p nonground_simpl
                     choice_candidates = heads_p simplified_prg
                     choice = head choice_candidates
                     queries = get_query_rules simplified_prg choice
                     mos = getpredval cons
                     gr_queries = concatMap (groundRule mos) queries
                    in
                    if (choice_candidates==[])
                      then putStrLn "No Choices left"
                      else
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
                       ++ "\nChoosenGRules:" ++ show_lp gr_queries
                       ++ "\n")


                        