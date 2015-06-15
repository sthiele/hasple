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
   SignedVar(..),
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

data SignedVar = T SVar
         | F SVar
         deriving (Show,Eq,Ord)

unsign:: SignedVar -> SVar
unsign (T l) = l
unsign (F l) = l

invert:: SignedVar -> SignedVar
invert (T l) = (F l)
invert (F l) = (T l)


-- -----------------------------------------
-- type Assignment = [Int]
type Assignment = Vector Int

initialAssignment:: Int -> Assignment
initialAssignment l =
  let x = fromList [0 | x <- [1..l]] in
  x


assign:: Assignment -> SignedVar -> Int -> Assignment
assign a (T l) dl = update a (fromList [(l,dl)])
assign a (F l) dl = update a (fromList [(l,-dl)])

unassign:: Assignment -> SignedVar -> Assignment
unassign a (T l) = update a (fromList [(l,0)])
unassign a (F l) = update a (fromList [(l,0)])

elemAss:: SignedVar -> Assignment -> Bool
elemAss (F l) a = (a ! l) < 0
elemAss (T l) a = ((a ! l) > 0)

isassigned:: SVar -> Assignment -> Bool
isassigned l a = ((a ! l) /= 0)

get_unassigned:: Assignment -> [SVar]
get_unassigned a = if Vector.null a
                   then []
                   else toList (findIndices (==0) a)

get_assigned:: Assignment -> [SVar]
get_assigned a = if Vector.null a
                 then []
                 else toList (findIndices (/=0) a)


get_tassigned:: Assignment -> [SVar]
get_tassigned a = if Vector.null a
                  then []
                  else toList (findIndices (>0) a)

get_fassigned:: Assignment -> [SVar]
get_fassigned a = if Vector.null a
                  then []
                  else toList (findIndices (<0) a)



-- get first assigned variable in the list
get_first_assigned_var:: Assignment -> SignedVar
get_first_assigned_var a  = get_first_assigned_var2 a 0

get_first_assigned_var2 a n =
  if n < (Vector.length a)
                             then
                               let val = a ! n in
                               case val of
                                 0 -> get_first_assigned_var2 a (n+1)
                                 _ -> if val > 0
                                         then (T n)
                                         else (F n)
                             else error "no more assigned variables"



falselits:: Assignment -> [SPVar] -> [SPVar]
falselits x spvars = falselits2 x spvars 0
falselits2 a spvars n =
  if n < Vector.length a
  then    case a ! n of
       (-1) -> ((get_lit n spvars):(falselits2 a spvars (n+1)))
       _  ->  (falselits2 a spvars (n+1))
  else []




trueatoms:: Assignment -> [SPVar] -> [Atom]
trueatoms x spvars = trueatoms2 x spvars 0
trueatoms2 a spvars n =
  if n < Vector.length a
  then
    if (a ! n) > 0
    then (atomsfromvar (get_lit n spvars)) Prelude.++ (trueatoms2 a spvars (n+1))
    else  (trueatoms2 a spvars (n+1))
  else []


falseatoms:: Assignment -> [SPVar] -> [Atom]
falseatoms x spvars = falseatoms2 x spvars 0
falseatoms2 a spvars n =
  if n < Vector.length a
  then
    if (a ! n) <0
    then (atomsfromvar (get_lit n spvars)) Prelude.++ (falseatoms2 a spvars (n+1))
    else (falseatoms2 a spvars (n+1))
  else []



-- -----------------------------------------
type Clause = ([SVar],[SVar])

joinClause:: Clause -> Clause -> Clause
joinClause (t1,f1) (t2,f2) = ( nub (t1 Prelude.++ t2),nub (f1 Prelude.++ f2))

without:: Clause -> Assignment -> Clause
without cl a = if Vector.null a
               then cl
               else without2 cl a 0
without2:: Clause -> Assignment -> Int -> Clause
without2 (t,f) a n =
  if (n < Vector.length a)
                  then
                    let val = a ! n in
                    case val of
                      0 -> without2 (t,f) a (n+1)
                      _ -> if val > 0
                           then without2 ((delete n t),f) a (n+1)
                           else without2 (t,(delete n f)) a (n+1)
                  else (t,f)


clauseWithoutSL:: Clause -> SignedVar -> Clause
clauseWithoutSL (t,f) (T l) = ((delete l t),f)
clauseWithoutSL (t,f) (F l) = (t,(delete l f))


elemClause:: SignedVar -> Clause -> Bool
elemClause a ([],[]) = False
elemClause (T l) (t,f) = Prelude.elem l t
elemClause (F l) (t,f) = Prelude.elem l f

