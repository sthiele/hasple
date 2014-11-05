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

p1 = [ (Rule "q" [] []),
       (Rule "p" ["q"] ["r"]) ]
       
p2 = [ (Rule "q" [] []),
       (Rule "p" ["p"] ["r"]) ] 
       
p3 = [ (Rule "p" [] ["q"]),
       (Rule "q" [] ["p"]) ] 
       
p4 = [ (Rule "p" [] ["p"])] 




show_lp [] = ""
show_lp (x:xs) = (show x) ++ "\n" ++ (show_lp xs)

show_as [] = "No Answersets"
show_as (x:xs) = (show_as2 (x:xs) 1)

show_as2 [] n = ""
show_as2 (x:xs) n = "\nAnswer " ++ (show n) ++ ":\n" ++ (show_as3 x) ++ "\n" ++ (show_as2 xs (n+1))

show_as3 [] = ""
show_as3 (x:xs) =  x ++ " " ++ (show_as3 xs)




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
           Left err -> putStrLn ("ParseError: " ++ show err)
           Right val -> putStrLn ("Program found:\n" ++ (show_lp val) ++ show_as (anssets val))
