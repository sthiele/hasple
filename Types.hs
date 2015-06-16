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
   asslen,
   initialAssignment,
   assign,
   unassign,
   backtrack,
   get_dlevel,
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
   elemClause,
   filter_dlevel,
   get_max_dlevel,
   only,
   RES(..),
   resolve,
   get_sigma,
  ) where
import ASP
import SPVar
import Data.List (nub, delete)
import Data.Vector.Unboxed as Vector
import Debug.Trace

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

asslen:: Assignment -> Int
asslen a  =
  trace ( "asslen: " Prelude.++ (show a)) $
  Vector.length a

assign:: Assignment -> SignedVar -> Int -> Assignment
assign a (T l) dl = update a (fromList [(l,dl)])
assign a (F l) dl = update a (fromList [(l,-dl)])

get_dlevel:: Assignment -> SignedVar -> Int
get_dlevel a (T l) = (a ! l)
get_dlevel a (F l) = -(a ! l)

unassign:: Assignment -> SignedVar -> Assignment
unassign a (T l) = update a (fromList [(l,0)])
unassign a (F l) = update a (fromList [(l,0)])

backtrack:: Assignment -> Int -> Assignment
backtrack a dl = backtrack2 a dl 0

backtrack2 a dl i =
  if i < (Vector.length a)
  then
    if abs ( a ! i ) < dl
    then backtrack2 a dl (i+1)
    else
      backtrack2 (unassign a (T i)) dl (i+1)
    else a

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
-- type Clause = ([SVar],[SVar])
type Clause = Vector Int


joinClause:: Clause -> Clause -> Clause
-- joinClause (t1,f1) (t2,f2) = ( nub (t1 Prelude.++ t2),nub (f1 Prelude.++ f2))
joinClause c1 c2 = joinClause2 c1 c2 0
joinClause2 c1 c2 i =
    if i < Vector.length c1
    then
      let x = c2 ! i in
      joinClause2 (update c1 (fromList [(i,x)])) c2 (i+1)
    else c1


without:: Clause -> Assignment -> Clause
without c a = without2 c a 0
without2 c a i =
    if i < Vector.length c
    then
      if (c!i) > 0
      then
        if (a!i) > 0
        then without2 (update c (fromList [(i,0)])) a (i+1)
        else without2 c a (i+1)
      else
        if (c!i) < 0
        then
          if (a!i) < 0
          then without2 (update c (fromList [(i,0)])) a (i+1)
          else without2 c a (i+1)
        else without2 c a (i+1)
    else c

clauseWithoutSL:: Clause -> SignedVar -> Clause
clauseWithoutSL c (T l) = if (c ! l) > 0
                          then unassign c (T l)   -- should be SVar l
                          else c
clauseWithoutSL c (F l) = if (c ! l) < 0
                          then unassign c (F l)   -- should be SVar l
                          else c


elemClause:: SignedVar -> Clause -> Bool
elemClause (T l) c = (c ! l) > 0
elemClause (F l) c = (c ! l) < 0



filter_dlevel:: Clause -> Assignment -> Int -> Clause
-- get rho in conflict_analysis
filter_dlevel c a l = filter_dlevel2 c a l 0
filter_dlevel2 c a l i =
  if i < Vector.length c
     then
       if (a ! i)==l
       then filter_dlevel2 c a l (i+1)
       else
         let c' = update c (fromList [(i,0)]) in
         filter_dlevel2 c' a l (i+1)
     else c


get_max_dlevel:: Clause -> Assignment -> Int
-- determin k in conflict_analysis
get_max_dlevel c a = get_max_dlevel2 c a 0 0

get_max_dlevel2 c a i akku =
  if i < Vector.length c
  then
    if (a!i) > akku
    then get_max_dlevel2 c a (i+1) (a!i)
    else get_max_dlevel2 c a (i+1) akku
  else akku


only:: Clause -> SignedVar -> Bool
-- returns True if the Signed Literal is the only in the assignment
only c (T l) =
  if (c!l) == 1
  then only2 c l 0
  else False
  
only c (F l) =
  if (c!l) == (-1)
  then only2 c l 0
  else False

  
only2 c l i =
  if i < Vector.length c
  then
    if (c!i) == 0
    then only2 c l (i+1)
    else
      if l==i
      then  only3 c (i+1)
      else False
  else True

only3 c i =
  if i < Vector.length c
  then
    if (c!i) == 0
    then only3 c (i+1)
    else False
  else True

  

data RES =  Res SignedVar
         | NIX
         | CONF


resolve:: Clause -> Assignment -> RES
resolve c a = resolvefirst c a 0

resolvefirst c a i =
  if i < Vector.length c
  then
     if (c!i) == 0
     then resolvefirst c a (i+1)
     else
       if (c!i) > 0 
       then
         if (a!i) > 0
         then resolvefirst c a (i+1)
         else resolvesecond c a (i+1) (F i)
       else -- c!i < 0
         if (a!i) < 0
         then resolvefirst c a (i+1) 
         else resolvesecond c a (i+1) (T i)
  else CONF

resolvesecond:: Clause -> Assignment -> Int -> SignedVar -> RES
resolvesecond c a i akku =
  if i < Vector.length c
  then
     if (c!i) == 0
     then resolvesecond c a (i+1) akku
     else
       if (c!i) > 0
       then
         if (a!i) > 0
         then resolvesecond c a (i+1) akku
         else NIX
       else -- c!i < 0
         if (a!i) < 0
         then resolvesecond c a (i+1) akku
         else NIX
 else Res akku





get_sigma:: Clause -> Assignment -> (SignedVar, Assignment)
-- used in conflict_analysis
get_sigma c a = get_sigma2 c a 0

get_sigma2 c a i =
  if i < Vector.length c
  then
    let prefix = unassign a (T i) in  -- TODO unassign latest
    if (c!i) > 0
    then
      let sigma = (T i)
          temp = without c prefix
      in
      if only temp sigma
      then (sigma, prefix)
      else get_sigma2 c prefix (i+1)   -- try next sigma
    else
      if (c!i) > 0
      then
        let sigma = (F i)
            temp = without c prefix
        in
        if only temp sigma
        then (sigma,prefix)
        else get_sigma2 c prefix (i+1)  -- try next sigma
      else get_sigma2 c prefix (i+1)    -- try next sigma
  else error "no sigma found"














  