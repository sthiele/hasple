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
-- import Grounder -- for old style grounding->solving
-- import Solver   -- for old style grounding->solving
import GrounderSolver -- for interleaved grounding/solving


get_answersets:: [Rule] -> Int -> [[Atom]]
-- get_answersets prg i = anssets (groundProgram prg) -- for old style grounding->solving
get_answersets prg i = outer  prg                     -- for interleaved grounding/solving

main :: IO ()  
main =
  do
    args <- getArgs
    if args==[]
       then putStrLn "No arguments given!"
       else do
         putStrLn ("Answer Set Solver in Haskell by Sven Thiele 2015.")
         contents <- readFile (head args)
         case readProgram contents of
           Left  err -> putStrLn ("ParseError: " ++ show err)
           Right val -> putStrLn $
                        show_as (get_answersets val 0)

            


