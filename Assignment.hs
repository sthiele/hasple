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
   assignment_size,
   assign,
   assign_trues,
   assign_falses,
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
   SymbolTable
) where


import ASP
import SPVar
import Data.List (nub, delete)
import Data.Vector.Unboxed as UVec
import Data.Vector as BVec
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


type SymbolTable = BVec.Vector SPVar

get_lit :: SymbolTable -> Int -> SPVar
get_lit st i = st BVec.! i


type Assignment = UVec.Vector Int

initialAssignment :: Int -> Assignment
initialAssignment l = UVec.fromList [ 0 | x <- [1..l]] 

assignment_size :: Assignment -> Int
assignment_size a = UVec.length a

assign :: Assignment -> SignedVar -> Int -> Assignment
assign a (T l) dl = a  UVec.// [(l,dl)]
assign a (F l) dl = a  UVec.// [(l,-dl)]

get_alevel :: Assignment -> SignedVar -> Int
get_alevel a (T l) = (a UVec.!l)
get_alevel a (F l) = -(a UVec.!l)


unassign :: Assignment -> SVar -> Assignment
unassign a l = a  UVec.// [(l,0)]
  

backtrack :: Assignment -> Int -> Assignment
backtrack a dl = backtrack2 a dl 0

backtrack2 a dl i =
  if i < (UVec.length a)
  then
    if (abs (a UVec.!i)) < dl
    then backtrack2 a dl (i+1)
    else backtrack2 (unassign a i) dl (i+1)
  else a

elemAss :: SignedVar -> Assignment -> Bool
elemAss (F l) a = (a  UVec.! l) < 0
elemAss (T l) a = ((a  UVec.! l) > 0)

isassigned :: SVar -> Assignment -> Bool
isassigned l a = ((a  UVec.! l) /= 0)

get_unassigned :: Assignment -> [SVar]
get_unassigned a = 
  if UVec.null a
  then []
  else UVec.toList (UVec.findIndices (==0) a)

get_assigned :: Assignment -> [SVar]
get_assigned a = 
  if UVec.null a
  then []
  else UVec.toList (UVec.findIndices (/=0) a)


get_tassigned :: Assignment -> [SVar]
get_tassigned a = 
  if UVec.null a
  then []
  else UVec.toList (UVec.findIndices (>0) a)

get_fassigned :: Assignment -> [SVar]
get_fassigned a = 
  if UVec.null a
  then []
  else UVec.toList (UVec.findIndices (<0) a)


falselits :: Assignment -> SymbolTable -> [SPVar]
falselits a st = Prelude.map (get_lit st) (get_fassigned a)

trueatoms :: Assignment -> SymbolTable -> [Atom]
trueatoms a st = Prelude.concatMap atomsfromvar (Prelude.map (get_lit st) (get_tassigned a))

falseatoms :: Assignment -> SymbolTable -> [Atom]
falseatoms a st = Prelude.concatMap atomsfromvar (Prelude.map (get_lit st) (get_fassigned a))

nonfalseatoms :: Assignment -> SymbolTable -> [Atom]
nonfalseatoms a st = Prelude.concatMap atomsfromvar (Prelude.map (get_lit st) (UVec.toList (UVec.findIndices (>=0) a)))

assign_trues :: Assignment -> [SVar] -> Assignment
assign_trues a [] = a
assign_trues a (v:vs) = assign_trues (assign a (T v) 1) vs

assign_falses :: Assignment -> [SVar] -> Assignment
assign_falses a [] = a
assign_falses a (v:vs) = assign_falses (assign a (F v) 1) vs



