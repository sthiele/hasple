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
import GrounderSolver -- for interleaved grounding/solving


get_answersets :: [Rule] -> Int -> [[Atom]]
-- get_answersets prg i = anssets (groundProgram prg)    -- for old style grounding->solving
get_answersets prg i = gr_solve prg                      -- for interleaved grounding/solving


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
        Right val -> let as = (get_answersets val 0) in
                     print_as as


print_as [] = putStr "No Answersets"
print_as l = print_as2 1 l

print_as2 n [] = putStr "\n"
print_as2 n (x:xs)  =
  do
    putStr "Answer "
    print n
    print_as3 x
    print_as2 (n+1) xs

print_as3 [] = putStr "\n"
print_as3 (x:xs) =
  do
    putStr (show x)
    putStr " "
    print_as3 xs


show_lp :: [Rule] -> [Char]
show_lp [] = ""
show_lp (x:xs) = (show x) ++ "\n" ++ (show_lp xs)


