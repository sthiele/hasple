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
   initialAssignment,
   assign,
   unassign,
   elemAss,
   isassigned,
   get_unassigned,
   get_assigned,
   get_tassigned,
   get_fassigned,
   get_first_assigned_var,
   falselits,
   trueatoms,
   falseatoms,
   Clause(..),
   joinClause,
   without,
   clauseWithoutSL,
   elemClause
  ) where
import ASP
import SPVar
import Data.List (nub, delete)
import Data.Vector.Unboxed as Vector


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
-- type Assignment = [Int]
type Assignment = Vector Int

initialAssignment:: Int -> Assignment
initialAssignment l =
  let x = fromList [0 | x <- [1..l]] in
--   trace ("test initAss" Prelude.++ (show x) Prelude.++ (show l) Prelude.++"\n")
--   $
  x


assign:: Assignment -> AssignedVar -> Assignment
-- assign a (T l) = (Prelude.take (l-1) a) Prelude.++ (1:(Prelude.drop l a))
-- assign a (F l) = (Prelude.take (l-1) a) Prelude.++ ((-1):(Prelude.drop l a))
assign a (T l) = update a (fromList [(l,1)])
assign a (F l) = update a (fromList [(l,-1)])

unassign:: Assignment -> AssignedVar -> Assignment
-- unassign a (T l) = (Prelude.take (l-1) a) Prelude.++ (0:(Prelude.drop l a))
-- unassign a (F l) = (Prelude.take (l-1) a) Prelude.++ (0:(Prelude.drop l a))
unassign a (T l) = update a (fromList [(l,0)])
unassign a (F l) = update a (fromList [(l,0)])

elemAss:: AssignedVar -> Assignment -> Bool
-- elemAss (T l) a = (Prelude.head (Prelude.drop (l-1) a))==1
-- elemAss (F l) a = (Prelude.head (Prelude.drop (l-1) a))==(-1)
elemAss (F l) a =
--   trace ("test elemAssF" Prelude.++ (show a) Prelude.++ (show l) Prelude.++"\n")
--   $
  not ((a ! l) == 0)
elemAss (T l) a =
--   trace ("test elemAssT" Prelude.++ (show a) Prelude.++ (show l) Prelude.++"\n")
--   $
  not ((a ! l) == 0)

isassigned:: SVar -> Assignment -> Bool
-- isassigned l a = (Prelude.head (Prelude.drop (l-1) a))/=0
isassigned l a =
--   trace ("test isassigned " Prelude.++ (show a) Prelude.++ (show l) Prelude.++"\n")
--   $
  not ((a ! l) == 0)

get_unassigned:: Assignment -> [SVar]
-- get_unassigned a = get_unassigned2 a 1
-- get_unassigned2 [] _ = []
-- get_unassigned2 (0:as) n = (n:(get_unassigned2 as (n+1)))
-- get_unassigned2 (_:as) n = (get_unassigned2 as (n+1))

get_unassigned a = if Vector.null a
                   then []
                   else toList (findIndices (==0) a)

get_assigned:: Assignment -> [SVar]
-- get_assigned a = get_assigned2 a 1
-- get_assigned2 [] _ = []
-- get_assigned2 (1:as) n = (n:(get_assigned2 as (n+1)))
-- get_assigned2 (-1:as) n = (n:(get_assigned2 as (n+1)))
-- get_assigned2 (_:as) n = (get_assigned2 as (n+1))
get_assigned a = if Vector.null a
                 then []
                 else toList (findIndices (/=0) a)


get_tassigned:: Assignment -> [SVar]
-- get_tassigned a = get_tassigned2 a 1
-- get_tassigned2 [] _ = []
-- get_tassigned2 (1:as) n = (n:(get_tassigned2 as (n+1)))
-- get_tassigned2 (_:as) n = (get_tassigned2 as (n+1))
get_tassigned a = if Vector.null a
                  then []
                  else toList (findIndices (==1) a)

get_fassigned:: Assignment -> [SVar]
-- get_fassigned a = get_fassigned2 a 1
-- get_fassigned2 [] _ = []
-- get_fassigned2 (-1:as) n = (n:(get_fassigned2 as (n+1)))
-- get_fassigned2 (_:as) n = (get_fassigned2 as (n+1))
get_fassigned a = if Vector.null a
                  then []
                  else toList (findIndices (==(-1)) a)



-- get first assigned variable in the list
get_first_assigned_var:: Assignment -> AssignedVar
-- get_first_assigned_var a = get_first_assigned_var2 a 1
-- get_first_assigned_var2 [] _ = error "no more assigned variables"
-- get_first_assigned_var2 (0:as) n = get_first_assigned_var2 as (n+1)
-- get_first_assigned_var2 (1:as) n = (T n)
-- get_first_assigned_var2 ((-1):as) n = (F n)

-- get_first_assigned_var a = get_first_assigned_var2 a 1
get_first_assigned_var a  = get_first_assigned_var2 a 0

get_first_assigned_var2 a n =
--   trace ("test get_first_assigned_var" Prelude.++ (show a) Prelude.++ (show n) Prelude.++"\n")
--   $
  if n < (Vector.length a)
                             then
                               case a ! n of
                                 0 -> get_first_assigned_var2 a (n+1)
                                 1 -> (T n)
                                 (-1) -> (F n)
                             else error "no more assigned variables"   



falselits:: Assignment -> [SPVar] -> [SPVar]
-- falselits x spvars = falselits2 x spvars 1
--
-- falselits2:: Assignment -> [SPVar] -> Int -> [SPVar]
--
-- falselits2 [] spvars n = []
--
-- falselits2 ((-1):as) spvars n = ((get_lit n spvars):(falselits2 as spvars (n+1)))
--
-- falselits2 (_:as) spvars n = (falselits2 as spvars (n+1))

falselits x spvars = falselits2 x spvars 0
falselits2 a spvars n =
--   trace ("test falselits" Prelude.++ (show a) Prelude.++ (show n) Prelude.++"\n")
--   $
  if n < Vector.length a
  then    case a ! n of
       (-1) -> ((get_lit n spvars):(falselits2 a spvars (n+1)))
       _  ->  (falselits2 a spvars (n+1))
  else []




trueatoms:: Assignment -> [SPVar] -> [Atom]
-- trueatoms x spvar = trueatoms2 x spvar 1
--
-- trueatoms2:: Assignment -> [SPVar] -> Int -> [Atom]
--
-- trueatoms2 [] _ _ = []
--
-- trueatoms2 (1:as) spvar n = (atomsfromvar (get_lit n spvar))++ (trueatoms2 as spvar (n+1))
--
-- trueatoms2 (_:as) spvar n = (trueatoms2 as spvar (n+1))


trueatoms x spvars = trueatoms2 x spvars 0
trueatoms2 a spvars n =
--   trace ("test trueatoms" Prelude.++ (show a) Prelude.++ (show n) Prelude.++"\n")
--   $
  if n < Vector.length a
  then
    case a ! n of
       (1) -> (atomsfromvar (get_lit n spvars)) Prelude.++ (trueatoms2 a spvars (n+1))
       _  ->  (trueatoms2 a spvars (n+1))
  else []


falseatoms:: Assignment -> [SPVar] -> [Atom]
-- falseatoms x spvar = falseatoms2 x spvar 1
-- 
-- falseatoms2:: Assignment -> [SPVar] -> Int -> [Atom]
-- 
-- falseatoms2 [] spvar n = []
-- 
-- falseatoms2 ((-1):as) spvar n = (atomsfromvar (get_lit n spvar))++ (falseatoms2 as spvar (n+1))
-- 
-- falseatoms2 (_:as) spvar n = (falseatoms2 as spvar (n+1))

falseatoms x spvars = falseatoms2 x spvars 0
falseatoms2 a spvars n =
--   trace ("test falseatoms" Prelude.++ (show a) Prelude.++ (show n) Prelude.++"\n")
--   $
  if n < Vector.length a
  then
    case a ! n of
       (-1) -> (atomsfromvar (get_lit n spvars)) Prelude.++ (falseatoms2 a spvars (n+1))
       _  ->  (falseatoms2 a spvars (n+1))
  else []

                                 

-- -----------------------------------------
type Clause = ([SVar],[SVar])

joinClause:: Clause -> Clause -> Clause
joinClause (t1,f1) (t2,f2) = ( nub (t1 Prelude.++ t2),nub (f1 Prelude.++ f2))

without:: Clause -> Assignment -> Clause
-- without cl as = without2 cl as 1
-- without2:: Clause -> Assignment -> Int -> Clause
-- without2 cl [] _ = cl
-- without2 cl (0:as) n = without2 cl as (n+1)
-- without2 (t,f) (1:as) n = without2 ((delete n t),f) as (n+1)
-- without2 (t,f) ((-1):as) n = without2 (t,(delete n f)) as (n+1)

without cl a = if Vector.null a
               then cl
               else without2 cl a 0
without2:: Clause -> Assignment -> Int -> Clause
without2 (t,f) a n =
--   trace ("t_without c"
--   Prelude.++ (show a)
--   Prelude.++ (show (Data.Vector.length a))
--   Prelude.++ (show n)
--   Prelude.++"\n")
--   $
  if (n < Vector.length a)
                  then
                    case a ! n of
                      0 -> without2 (t,f) a (n+1)
                      1 -> without2 ((delete n t),f) a (n+1)
                      (-1) -> without2 (t,(delete n f)) a (n+1)
                  else (t,f)


clauseWithoutSL:: Clause -> AssignedVar -> Clause
clauseWithoutSL (t,f) (T l) = ((delete l t),f)
clauseWithoutSL (t,f) (F l) = (t,(delete l f))


elemClause:: AssignedVar -> Clause -> Bool
elemClause a ([],[]) = False
elemClause (T l) (t,f) = Prelude.elem l t
elemClause (F l) (t,f) = Prelude.elem l f

