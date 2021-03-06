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

module Test (
  unit_test,
  test,
)where
import Test.QuickCheck

import ASP
import Grounder
import qualified GoodSolver
-- import qualified CDNLSolverST
import GrounderSolverST
-- import STTest

import LPParser -- for parsing tests
import Data.List (sort)
import Debug.Trace


-- function to test

test_good :: [Char] -> [[Atom]]
test_good x =
  do
    case readProgram x of
      Left  err -> []
      Right prg -> sort (map sort (GoodSolver.anssets (groundProgram prg)))


-- test_old :: [Char] -> [[Atom]]
-- test_old x =
--   do
--     case readProgram x of
--       Left  err -> []
--       Right prg -> sort (map sort (CDNLSolver.anssets (groundProgram prg)))


test_new :: [Char] -> [[Atom]]
test_new x =
  do
    case readProgram x of
      Left  err -> []
      Right prg -> sort (map sort (gr_solve prg))

test :: [Char] -> IO()
test x =
  do
    case readProgram x of
      Left  err -> print $ "ParseError: " ++ (show err)
      Right prg -> putStrLn $ show (gr_solve prg)






good_solver p = sort (map sort (GoodSolver.anssets (groundProgram p)))
new_solver  p = sort (map sort (gr_solve p))

-- Test properties

prop_good_model p = new_solver p == good_solver p


-- Test cases logic programs

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
Right mp13 = readProgram mpr13



-- test 

t0 = quickCheck prop_good_model

t1 = (test_new mpr1)==(test_good mpr1)
t2 = (test_new mpr2)==(test_good mpr2) 
t3 = (test_new mpr3)==(test_good mpr3) 
t4 = (test_new mpr4)==(test_good mpr4) 
t5 = (test_new mpr5)==(test_good mpr5) 
t6 = (test_new mpr6)==(test_good mpr6)
t7 = (test_new mpr6a)==(test_good mpr6a) 
t8 = (test_new mpr6b)==(test_good mpr6b) 
t9 = (test_new mpr7)==(test_good mpr7)
-- t10 = (test_new mpr8)==(test_good mpr8)   -- test takes too long
-- t11 = (test_new mpr9)==(test_good mpr9)   -- test takes too long
t12 = (test_new mpr10)==(test_good mpr10) 
t13 = (test_new mpr11)==(test_good mpr11) 
t14 = (test_new mpr12)==(test_good mpr12) 
t15 = (test_new mpr13)==(test_good mpr13)


unit_test =
  trace ("test1:  " ++ (show t1)) $
  trace ("test2:  " ++ (show t2)) $
  trace ("test3:  " ++ (show t3)) $
  trace ("test4:  " ++ (show t4)) $
  trace ("test5:  " ++ (show t5)) $
  trace ("test6:  " ++ (show t6)) $
  trace ("test7:  " ++ (show t7)) $
  trace ("test8:  " ++ (show t8)) $
  trace ("test9:  " ++ (show t9)) $
  trace ("test12: " ++ (show t12)) $
  trace ("test13: " ++ (show t13)) $
  trace ("test14: " ++ (show t14)) $
  trace ("test15: " ++ (show t15)) $
  t1&&t2&&t3&&t4&&t5&&t6&&t7&&t8&&t9&&t12&&t13&&t14&&t15
  
 



