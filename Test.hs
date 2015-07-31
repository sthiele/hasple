module Test (
  unit_test,
  test,
)where
import ASP
import Grounder
import CDNLSolver
import GoodSolver
import GrounderSolver
import LPParser -- for parsing tests
import Data.List (sort)
import Debug.Trace

test_good:: [Char] -> [[Atom]]
test_good x =
  do
    case readProgram x of
      Left  err -> []
      Right prg -> sort (map sort (anssets (groundProgram prg)))


test_old:: [Char] -> [[Atom]]
test_old x =
  do
    case readProgram x of
      Left  err -> []
      Right prg -> sort (map sort (cdnl_enum (groundProgram prg) 0))


test_new:: [Char] -> [[Atom]]
test_new x =
  do
    case readProgram x of
      Left  err -> []
      Right prg -> sort (map sort (gr_solve prg))

test:: [Char] -> IO()
test x =
  do
    case readProgram x of
      Left  err -> print $ "ParseError: " ++ (show err)
      Right prg -> putStrLn $ show (gr_solve prg)


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
Right mp13 = readProgram mpr13

unit_test =
  let t1 = (test_new mpr1)==(test_good mpr1) 
      t2 = (test_new mpr2)==(test_good mpr2) 
      t3 = (test_new mpr3)==(test_good mpr3) 
      t4 = (test_new mpr4)==(test_good mpr4) 
      t5 = (test_new mpr5)==(test_good mpr5) 
      t6 = (test_new mpr6)==(test_good mpr6)
      t7 = (test_new mpr6a)==(test_good mpr6a) 
      t8 = (test_new mpr6b)==(test_good mpr6b) 
      t9 = (test_new mpr7)==(test_good mpr7)   -- infinite
--       t10 = (test_new mpr8)==(test_good mpr8)   -- test takes too long
--       t11 = (test_new mpr9)==(test_good mpr9)   -- test takes too long
      t12 = (test_new mpr10)==(test_good mpr10) 
      t13 = (test_new mpr11)==(test_good mpr11) 
      t14 = (test_new mpr12)==(test_good mpr12) 
      t15 = (test_new mpr13)==(test_good mpr13)
  in
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
  
  
