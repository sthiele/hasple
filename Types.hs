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
   get_dlevel_alevel,
   elemAss,
   isassigned,
   get_unassigned,
   get_assigned,
   get_tassigned,
   get_fassigned,
   falselits,
   trueatoms,
   falseatoms,
   Clause(..),
   joinClause,
   without,
   clauseWithoutSL,
   elemClause,
--    filter_dlevel,
   get_max_dlevel_alevel,
   only,
   RES(..),
   resolve,
   get_sigma,
   filter_dl_al,
   is_included
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

get_dlevel_alevel:: Assignment -> SignedVar -> Int
get_dlevel_alevel a (T l) = (a ! l)
get_dlevel_alevel a (F l) = -(a ! l)

unassign:: Assignment -> SignedVar -> Assignment
unassign a (T l) = update a (fromList [(l,0)])
unassign a (F l) = update a (fromList [(l,0)])

backtrack:: Assignment -> Int -> Assignment
backtrack a dl = backtrack2 a dl 0

backtrack2 a dl i =
  if i < (Vector.length a)
  then
    if (abs (a!i)) < dl
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








falselits:: Assignment -> [SPVar] -> [SPVar]
falselits x spvars = falselits2 x spvars 0
falselits2 a spvars i =
  if i < Vector.length a
  then if (a!i) < 0
       then ((get_lit i spvars):(falselits2 a spvars (i+1)))
       else (falselits2 a spvars (i+1))
  else []


trueatoms:: Assignment -> [SPVar] -> [Atom]
trueatoms x spvars = trueatoms2 x spvars 0
trueatoms2 a spvars i =
  if i < Vector.length a
  then
    if (a!i) > 0
    then (atomsfromvar (get_lit i spvars)) Prelude.++ (trueatoms2 a spvars (i+1))
    else  (trueatoms2 a spvars (i+1))
  else []


falseatoms:: Assignment -> [SPVar] -> [Atom]
falseatoms x spvars = falseatoms2 x spvars 0
falseatoms2 a spvars i =
  if i < Vector.length a
  then
    if (a!i) <0
    then (atomsfromvar (get_lit i spvars)) Prelude.++ (falseatoms2 a spvars (i+1))
    else (falseatoms2 a spvars (i+1))
  else []



-- -----------------------------------------
type Clause = Vector Int

joinClause:: Clause -> Clause -> Clause
joinClause c1 c2 = joinClause2 c1 c2 0
joinClause2 c1 c2 i =
    if i < Vector.length c1
    then
      if (c2!i) /= 0
      then joinClause2 (update c1 (fromList [(i,(c2!i))])) c2 (i+1)
      else joinClause2 c1 c2 (i+1)
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
clauseWithoutSL c (T l) =
  if (c ! l) > 0
  then unassign c (T l)   -- should be SVar l
  else c
clauseWithoutSL c (F l) =
  if (c ! l) < 0
  then unassign c (F l)   -- should be SVar l
  else c


elemClause:: SignedVar -> Clause -> Bool
elemClause (T l) c = (c ! l) > 0
elemClause (F l) c = (c ! l) < 0






get_max_dlevel_alevel:: Clause -> Assignment -> Int
-- determin k in conflict_analysis
get_max_dlevel_alevel c a = get_max_dlevel_alevel2 c a 0 0

get_max_dlevel_alevel2 c a i akku =
  if i < Vector.length c
  then
    if (a!i) > akku
    then get_max_dlevel_alevel2 c a (i+1) (a!i)
    else get_max_dlevel_alevel2 c a (i+1) akku
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


get_last_assigned_var:: Clause -> Assignment -> SVar
-- get last assigned variable in the list
get_last_assigned_var c a  = get_last_assigned_var2 c a 0

get_last_assigned_var2 c a n =
  if n < (Vector.length c)
  then
    if (c!n) == 0
    then get_last_assigned_var2 c a (n+1)
    else
       let val = a ! n in
       case val of
         0 -> get_last_assigned_var2 c a (n+1)
         _ -> get_last_assigned_var3 c a (n+1) (n, abs val)
  else error "no more assigned variables"

get_last_assigned_var3 c a n (akku,akkuval) =
  if n < (Vector.length c)
  then
    if (c!n) == 0
    then get_last_assigned_var3 c a (n+1) (akku,akkuval)
    else
       let val = a ! n in
       if abs val > akkuval
       then get_last_assigned_var3 c a (n+1) (n, abs val)
       else get_last_assigned_var3 c a (n+1) (akku,akkuval)
   else akku


get_sigma:: Clause -> Assignment -> Int -> (SignedVar, Assignment)
-- used in conflict_analysis

-- get_sigma c a 1 = get_sigma2 c a 3  -- mpr 5
-- get_sigma c a 2 = get_sigma2 c a 2
-- get_sigma c a 3 = get_sigma2 c a 1

-- get_sigma c a 1 = get_sigma2 c a 8  -- mpr 6
-- get_sigma c a 2 = get_sigma2 c a 4
-- get_sigma c a 3 = get_sigma2 c a 5


get_sigma c a i =
  let last_assigned_var = get_last_assigned_var c a in
--   trace ("lastvar: " Prelude.++ (show c) Prelude.++ (show a) Prelude.++ (show last_assigned_var)) $
  get_sigma2 c a last_assigned_var

get_sigma2 c a i =
--   trace ("get_sigma: " Prelude.++ (show c) Prelude.++ (show a) Prelude.++ (show i)) $
  if i < Vector.length c
  then
  let prefix = unassign a (T i)   in
--     trace ("prefix: " Prelude.++ (show prefix) ) $
    if (c!i) > 0
    then
      let sigma = (T i)
          temp = without c prefix
      in
--       trace ("temp: " Prelude.++ (show temp) ) $
      if only temp sigma
      then (sigma, prefix)
      else get_sigma2 c a (i+1)   -- try next sigma
    else
      if (c!i) < 0
      then
        let sigma = (F i)
            temp = without c prefix
        in
--         trace ("temp: " Prelude.++ (show temp) ) $
        if only temp sigma
        then (sigma,prefix)
        else get_sigma2 c a (i+1)  -- try next sigma
      else get_sigma2 c a (i+1)    -- try next sigma
  else error "no sigma found"



filter_dl_al:: Clause -> Assignment -> Int -> Clause
filter_dl_al c a l = filter_dl_al2 c a l 0
filter_dl_al2:: Clause -> Assignment -> Int -> Int -> Clause
filter_dl_al2 c a l i =
  if i < Vector.length c
  then
     if (abs (a!i)) < l
     then
       let c' = update c (fromList [(i,0)]) in
       filter_dl_al2 c' a l (i+1)
     else filter_dl_al2 c a l (i+1)
  else c



is_included:: Clause -> Assignment -> Bool
is_included c a = is_included2 c a 0
is_included2:: Clause -> Assignment -> Int -> Bool
is_included2 c a i =
  if i < Vector.length c
  then
    if (a!i) > 0
    then
      if (c!i) < 0
      then False
      else is_included2 c a (i+1)
    else
      if (a!i) < 0
      then
        if (c!i) > 0
        then False
        else is_included2 c a (i+1)
      else -- (a!i) == 0
        if (c!i) == 0
        then is_included2 c a (i+1)
        else False
  else True


