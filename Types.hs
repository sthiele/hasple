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

-- {-# LANGUAGE MagicHash #-}
-- {-# LANGUAGE UnboxedTuples         #-}

import ASP
import SPVar
import Data.List (nub, delete)
import Data.Vector.Unboxed as Vector
import Debug.Trace

type SVar = Int

data SignedVar = T SVar
               | F SVar
               deriving (Show,Eq,Ord)

unsign :: SignedVar -> SVar
unsign (T l) = l
unsign (F l) = l

invert :: SignedVar -> SignedVar
invert (T l) = F l
invert (F l) = T l


-- -----------------------------------------

type Assignment = Vector Int

initialAssignment :: Int -> Assignment
initialAssignment l = fromList [ 0 | x <- [1..l]] 


assign :: Assignment -> SignedVar -> Int -> Assignment
assign a (T l) dl = a // [(l,dl)]
assign a (F l) dl = a // [(l,-dl)]

get_alevel :: Assignment -> SignedVar -> Int
get_alevel a (T l) = (a!l)
get_alevel a (F l) = -(a!l)


unassign :: Assignment -> SVar -> Assignment
unassign a l = a // [(l,0)]
  

backtrack :: Assignment -> Int -> Assignment
backtrack a dl = backtrack2 a dl 0

backtrack2 a dl i =
  if i < (Vector.length a)
  then
    if (abs (a!i)) < dl
    then backtrack2 a dl (i+1)
    else
      backtrack2 (unassign a i) dl (i+1)
  else a

elemAss :: SignedVar -> Assignment -> Bool
elemAss (F l) a = (a ! l) < 0
elemAss (T l) a = ((a ! l) > 0)

isassigned :: SVar -> Assignment -> Bool
isassigned l a = ((a ! l) /= 0)

get_unassigned :: Assignment -> [SVar]
get_unassigned a = if Vector.null a
                   then []
                   else toList (findIndices (==0) a)

get_assigned :: Assignment -> [SVar]
get_assigned a = if Vector.null a
                 then []
                 else toList (findIndices (/=0) a)


get_tassigned :: Assignment -> [SVar]
get_tassigned a = if Vector.null a
                  then []
                  else toList (findIndices (>0) a)

get_fassigned :: Assignment -> [SVar]
get_fassigned a = if Vector.null a
                  then []
                  else toList (findIndices (<0) a)


get_lit :: [SPVar] -> Int -> SPVar
get_lit spvars 0 = Prelude.head spvars
get_lit (v:vs) n = get_lit vs (n-1)


falselits :: Assignment -> [SPVar] -> [SPVar]
falselits a spvars = Prelude.map (get_lit spvars) (get_fassigned a)

trueatoms :: Assignment -> [SPVar] -> [Atom]
trueatoms a spvars =  Prelude.concatMap atomsfromvar (Prelude.map (get_lit spvars) (get_tassigned a))

falseatoms :: Assignment -> [SPVar] -> [Atom]

falseatoms a spvars =  Prelude.concatMap atomsfromvar (Prelude.map (get_lit spvars) (get_fassigned a))


nonfalseatoms :: Assignment -> [SPVar] -> [Atom]
nonfalseatoms a spvars = Prelude.concatMap atomsfromvar (Prelude.map (get_lit spvars) (toList (findIndices (>=0) a)))


-- -----------------------------------------

type Clause = ((Vector Int), Int, Int)

joinClauses :: Clause -> Clause -> Clause
joinClauses c1 c2 = joinClauses2 c1 c2 0
joinClauses2 (c1,w1,v1) (c2,w2,v2) i =
  if i < Vector.length c1
  then
    if (c2!i) /= 0
    then joinClauses2 ((c1 // [(i,(c2!i))]),w1,v1) (c2,w2,v2) (i+1)
    else joinClauses2 (c1,w1,v1) (c2,w2,v2) (i+1)
  else (c1,w1,v1)


without :: Assignment -> Assignment -> Assignment
without c a = without2 c a 0
without2 c a i =
  if i < Vector.length c
  then
    if (c!i) > 0
    then
      if (a!i) > 0
      then without2 (c // [(i,0)]) a (i+1)
        else without2 c a (i+1)
    else
      if (c!i) < 0
      then
        if (a!i) < 0
        then without2 (c // [(i,0)]) a (i+1)
        else without2 c a (i+1)
      else without2 c a (i+1)
  else c



clauseWithoutSL :: Clause -> SignedVar -> Clause
clauseWithoutSL (c,w,v) (T l) =
  if (c ! l) > 0
  then (unassign c l,w,v)
  else (c,w,v)
clauseWithoutSL (c,w,v) (F l) =
  if (c ! l) < 0
  then (unassign c l,w,v)
  else (c,w,v)


get_max_alevel :: Clause -> Assignment -> Int
-- determin k in conflict_analysis
get_max_alevel (c,w,v) a = get_max_alevel2 c a 0 0

get_max_alevel2 c a i akku =
  if i < Vector.length c
  then
    if (a!i) > akku
    then get_max_alevel2 c a (i+1) (a!i)
    else get_max_alevel2 c a (i+1) akku
  else akku


only :: Assignment -> SignedVar -> Bool
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



data RES = Res Assignment
         | ResU Assignment Clause
         | NIX
         | NIXU Clause         
         | CONF


resolve :: Int -> Clause -> Assignment -> RES

resolve al (c,w,v) a =
  if w == v -- unit clause
  then 
    if (a!w > 0 && c!w > 0) ||  (a!w < 0 && c!w < 0)
    then CONF
    else
      if c!w > 0 && a!w==0
      then Res (assign a (F w) al)
      else
        if c!w < 0 && a!w==0
        then Res (assign a (T w) al)
        else NIX
  else
  if (a!w > 0 && c!w > 0) ||  (a!w < 0 && c!w < 0)            -- assigned
  then updatewatch1 al (c,w,v) a
  else
    if (a!v > 0 && c!v > 0) || (a!v < 0 && c!v < 0)           -- assigned
    then updatewatch2 al (c,w,v) a
    else NIX
 

updatewatch1 :: Int -> (Vector Int, Int, Int) -> Assignment -> RES 
updatewatch1 al (c,w,v) a =
  case new_watch1 (c,0,v) a of
  Just (c',w',v') -> if (a!v > 0 && c!v > 0) || (a!v < 0 && c!v < 0) -- assigned
                     then updatewatch2x al (c',w',v') a
                     else NIXU (c',w',v')
  Nothing         -> if (a!v > 0 && c!v > 0)                         -- assigned true
                     then CONF
                     else
                       if (a!v < 0 && c!v < 0)                       -- assigned false
                       then CONF
                       else
                         if (a!v) == 0
                         then
                           if c!v > 0
                           then Res (assign a (F v) al)
                           else Res (assign a (T v) al)
                         else NIX

updatewatch2 al (c,w,v) a =
  case new_watch2 (c,w,0) a of
  Just (c,w',v') -> NIXU (c,w,v')
  Nothing        -> if (a!w) == 0
                    then
                      if c!w > 0
                      then Res (assign a (F w) al)
                      else Res (assign a (T w) al)
                    else NIX

updatewatch2x al (c,w,v) a =
  case new_watch2 (c,w,0) a of
  Just (c',w',v') -> NIXU (c,w,v')
  Nothing         -> if (a!w) == 0
                     then
                       if c!w > 0
                       then ResU (assign a (F w) al) (c,w,v)
                       else ResU (assign a (T w) al) (c,w,v)
                     else NIXU (c,w,v)
  
new_watch1 :: Clause -> Assignment -> Maybe Clause
new_watch1 (c,i,v) a =
  if i < Vector.length c
  then
    if c!i == 0
    then new_watch1 (c,(i+1),v) a
    else
      if i == v
      then new_watch1 (c,(i+1),v) a
      else
        if (a!i > 0 && c!i > 0) ||  (a!i < 0 && c!i < 0)  -- assigned
        then new_watch1 (c,(i+1),v) a 
        else Just (c,i,v)       
  else Nothing



new_watch2 :: Clause -> Assignment -> Maybe Clause
new_watch2 (c,w,i) a =
  if i < Vector.length c
  then
    if c!i == 0
    then new_watch2 (c,w,(i+1)) a
    else
      if i == w
      then new_watch2 (c,w,(i+1)) a
      else
        if (a!i > 0 && c!i > 0) ||  (a!i < 0 && c!i < 0)   -- assigned
        then new_watch2 (c,w,(i+1)) a
        else Just (c,w,i)
  else Nothing  
  

get_last_assigned_var :: Assignment -> Assignment -> SVar
-- get last assigned variable in the list
get_last_assigned_var c a  = get_last_assigned_var2 c a 0

get_last_assigned_var2 c a n =
  if n < (Vector.length c)
  then
    if (c!n) == 0
    then get_last_assigned_var2 c a (n+1)
    else
       let val = a!n in
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
       let val = a!n in
       if abs val > akkuval
       then get_last_assigned_var3 c a (n+1) (n, abs val)
       else get_last_assigned_var3 c a (n+1) (akku,akkuval)
   else akku


get_sigma :: Clause -> Assignment -> (SignedVar, Assignment)
-- used in conflict_analysis
get_sigma (c,w,v) a =
  let last_assigned_var = get_last_assigned_var c a in
  get_sigma2 c a last_assigned_var

get_sigma2 c a i =
  if i < Vector.length c
  then
  let prefix = unassign a i in
    if (c!i) > 0
    then
      let sigma = (T i)
          temp  = without c prefix
      in
      if only temp sigma
      then (sigma, prefix)
      else get_sigma2 c a (i+1)   -- try next sigma
    else
      if (c!i) < 0
      then
        let sigma = (F i)
            temp  = without c prefix
        in
        if only temp sigma
        then (sigma,prefix)
        else get_sigma2 c a (i+1)  -- try next sigma
      else get_sigma2 c a (i+1)    -- try next sigma
  else error "no sigma found"



filter_al :: Clause -> Assignment -> Int -> Assignment
-- unassigns all literal from c that have in a an alevel < l
filter_al (c,w,v) a l = filter_al2 c a l 0
filter_al2 :: Assignment -> Assignment -> Int -> Int -> Assignment
filter_al2 c a l i =
  if i < Vector.length c
  then
     if (abs (a!i)) < l
     then
       let c' = c // [(i,0)] in
       filter_al2 c' a l (i+1)
     else filter_al2 c a l (i+1)
  else c



is_included :: Clause -> Assignment -> Bool
is_included (c,w,v) a = is_included2 c a 0
is_included2 :: Assignment -> Assignment -> Int -> Bool
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

