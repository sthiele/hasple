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

module Types (
   SVar(..),
   AssignedVar(..),
   unsign,
   invert,
   Assignment(..),   
   assign,
   unassign,
   elemAss,
   isassigned,
   get_unassigned,
   get_first_assigned_var,
   Clause(..),
   joinClause,
   without,
   clauseWithoutSL,
   elemClause
  ) where
import ASP
import Data.List (nub, delete)

-- -------------------
type SVar = Int

data AssignedVar = T SVar
         | F SVar
         deriving (Show,Eq,Ord)

unsign:: AssignedVar -> SVar
unsign (T l) = l
unsign (F l) = l

invert:: AssignedVar -> AssignedVar
invert (T l) = (F l)
invert (F l) = (T l)


-- -----------------------------------------
type Assignment = [Integer]

assign:: Assignment -> AssignedVar -> Assignment
assign a (T l) = (take (l-1) a) ++ [1] ++ (drop l a)
assign a (F l) = (take (l-1) a) ++ [-1] ++ (drop l a)         

unassign:: Assignment -> AssignedVar -> Assignment
unassign a (T l) = (take (l-1) a) ++ [0] ++ (drop l a)
unassign a (F l) = (take (l-1) a) ++ [0] ++ (drop l a)

elemAss:: AssignedVar -> Assignment -> Bool
elemAss (T l) a = (head (drop (l-1) a))==1
elemAss (F l) a = (head (drop (l-1) a))==(-1)

isassigned:: SVar -> Assignment -> Bool
isassigned l a = (head (drop (l-1) a))/=0

get_unassigned:: Assignment -> [SVar]
get_unassigned a = get_unassigned2 a 1
get_unassigned2 [] _ = []
get_unassigned2 (0:as) n = (n:(get_unassigned2 as (n+1)))
get_unassigned2 (_:as) n = (get_unassigned2 as (n+1))


-- get first assigned variable in the list
get_first_assigned_var:: Assignment -> AssignedVar
get_first_assigned_var a = get_first_assigned_var2 a 1
get_first_assigned_var2 [] _ = error "no more assigned variables"
get_first_assigned_var2 (0:as) n = get_first_assigned_var2 as (n+1)
get_first_assigned_var2 (1:as) n = (T n)
get_first_assigned_var2 ((-1):as) n = (F n)


-- -----------------------------------------
type Clause = ([SVar],[SVar])

joinClause:: Clause -> Clause -> Clause
joinClause (t1,f1) (t2,f2) = ( nub (t1++t2),nub (f1++f2))

without:: Clause -> Assignment -> Clause
without cl as = without2 cl as 1
without2:: Clause -> Assignment -> Int -> Clause
without2 cl [] _ = cl
without2 cl (0:as) n = without2 cl as (n+1)
without2 (t,f) (1:as) n = without2 ((delete n t),f) as (n+1)
without2 (t,f) ((-1):as) n = without2 (t,(delete n f)) as (n+1)


clauseWithoutSL:: Clause -> AssignedVar -> Clause
clauseWithoutSL (t,f) (T l) = ((delete l t),f)
clauseWithoutSL (t,f) (F l) = (t,(delete l f))


elemClause:: AssignedVar -> Clause -> Bool
elemClause a ([],[]) = False
elemClause (T l) (t,f) = elem l t
elemClause (F l) (t,f) = elem l f

