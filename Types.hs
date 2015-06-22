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
   SVar,
   SignedVar(..),
   unsign,
   invert,
   Assignment,
   initialAssignment,
   assign,
   unassign,
   backtrack,
   get_alevel,
   elemAss,
   isassigned,
   get_unassigned,
   falselits,
   trueatoms,
   falseatoms,
   nonfalseatoms,
   Clause,
   joinClauses,
   clauseWithoutSL,
   get_max_alevel,
   only,
   RES(..),
   resolve,
   get_sigma,
   filter_al,
   is_included
) where
  
import ASP
import SPVar
import Data.List (nub, delete)
import Data.Vector.Unboxed as Vector
-- import Debug.Trace

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

type Assignment = Vector Int

initialAssignment:: Int -> Assignment
initialAssignment l =
  let x = fromList [0 | x <- [1..l]] in
  x


assign:: Assignment -> SignedVar -> Int -> Assignment
assign a (T l) dl = update a (fromList [(l,dl)])
assign a (F l) dl = update a (fromList [(l,-dl)])

get_alevel:: Assignment -> SignedVar -> Int
get_alevel a (T l) = (a ! l)
get_alevel a (F l) = -(a ! l)


unassign:: Assignment -> SVar -> Assignment
unassign a l = update a (fromList [(l,0)])


backtrack:: Assignment -> Int -> Assignment
backtrack a dl = backtrack2 a dl 0

backtrack2 a dl i =
  if i < (Vector.length a)
  then
    if (abs (a!i)) < dl
    then backtrack2 a dl (i+1)
    else
      backtrack2 (unassign a i) dl (i+1)
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


get_lit:: [SPVar] -> Int -> SPVar
get_lit spvars 0 = Prelude.head spvars
get_lit (v:vs) n = get_lit vs (n-1)


falselits:: Assignment -> [SPVar] -> [SPVar]
falselits a spvars = Prelude.map (get_lit spvars) (get_fassigned a)

trueatoms:: Assignment -> [SPVar] -> [Atom]
trueatoms a spvars =  Prelude.concatMap atomsfromvar (Prelude.map (get_lit spvars) (get_tassigned a))

falseatoms:: Assignment -> [SPVar] -> [Atom]

falseatoms a spvars =  Prelude.concatMap atomsfromvar (Prelude.map (get_lit spvars) (get_fassigned a))


nonfalseatoms:: Assignment -> [SPVar] -> [Atom]
nonfalseatoms a spvars = Prelude.concatMap atomsfromvar (Prelude.map (get_lit spvars) (toList (findIndices (>=0) a)))


-- -----------------------------------------

type Clause = Vector Int

joinClauses:: Clause -> Clause -> Clause
joinClauses c1 c2 = joinClauses2 c1 c2 0
joinClauses2 c1 c2 i =
    if i < Vector.length c1
    then
      if (c2!i) /= 0
      then joinClauses2 (update c1 (fromList [(i,(c2!i))])) c2 (i+1)
      else joinClauses2 c1 c2 (i+1)
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
  then unassign c l
  else c
clauseWithoutSL c (F l) =
  if (c ! l) < 0
  then unassign c l
  else c


get_max_alevel:: Clause -> Assignment -> Int
-- determin k in conflict_analysis
get_max_alevel c a = get_max_alevel2 c a 0 0

get_max_alevel2 c a i akku =
  if i < Vector.length c
  then
    if (a!i) > akku
    then get_max_alevel2 c a (i+1) (a!i)
    else get_max_alevel2 c a (i+1) akku
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


get_sigma:: Clause -> Assignment -> (SignedVar, Assignment)
-- used in conflict_analysis
get_sigma c a =
  let last_assigned_var = get_last_assigned_var c a in
--   trace ("lastvar: " Prelude.++ (show c) Prelude.++ (show a) Prelude.++ (show last_assigned_var)) $
  get_sigma2 c a last_assigned_var

get_sigma2 c a i =
--   trace ("get_sigma: " Prelude.++ (show c) Prelude.++ (show a) Prelude.++ (show i)) $
  if i < Vector.length c
  then
  let prefix = unassign a i in
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



filter_al:: Clause -> Assignment -> Int -> Clause
filter_al c a l = filter_al2 c a l 0
filter_al2:: Clause -> Assignment -> Int -> Int -> Clause
filter_al2 c a l i =
  if i < Vector.length c
  then
     if (abs (a!i)) < l
     then
       let c' = update c (fromList [(i,0)]) in
       filter_al2 c' a l (i+1)
     else filter_al2 c a l (i+1)
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


