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

module Assignment (
   Assignment,
   initAssignment,
   length,
   assign,
   unassign,
   backtrack,
   get_alevel,
   elem,
   unassigned,
   falselits,
   trueatoms,
   falseatoms,
   nonfalseatoms,
) where

import Prelude ((+), abs)
import Data.Int
import Data.Bool
import Data.Eq
import Data.Ord
import ASP
import SPVar
import qualified Data.List as List
import qualified Data.Vector.Unboxed as UVec
-- import Debug.Trace


type Assignment = UVec.Vector Int


initAssignment :: Int -> Assignment
-- create an initial assignment
initAssignment l = UVec.fromList [ 0 | x <- [1..l]] 


length :: Assignment -> Int
-- return the length of the assignment
length a = UVec.length a


assign :: Assignment -> SignedVar -> Int -> Assignment
-- assign a variable at an assignment level
assign a (T l) dl = a  UVec.// [(l,dl)]
assign a (F l) dl = a  UVec.// [(l,-dl)]


get_alevel :: Assignment -> SignedVar -> Int
-- return the assignment level of a variable
get_alevel a (T l) = (a UVec.!l)
get_alevel a (F l) = -(a UVec.!l)


unassign :: Assignment -> SVar -> Assignment
-- unassign a variable
unassign a l = a  UVec.// [(l,0)]
  

backtrack :: Assignment -> Int -> Assignment
-- backtrack the assignment to a decision level
backtrack a dl = backtrack2 a dl 0

backtrack2 a dl i =
  if i < (UVec.length a)
  then
    if (abs (a UVec.!i)) < dl
    then backtrack2 a dl (i+1)
    else backtrack2 (unassign a i) dl (i+1)
  else a


elem :: SignedVar -> Assignment -> Bool
-- return true if the signed variable is in the assignment
elem (F l) a = (a  UVec.! l) < 0
elem (T l) a = ((a  UVec.! l) > 0)


unassigned :: Assignment -> [SVar]
-- return a list of unassigned variables
unassigned a = 
  if UVec.null a
  then []
  else UVec.toList (UVec.findIndices (==0) a)


get_tassigned :: Assignment -> [SVar]
-- return a list of variables assigned to true
get_tassigned a = 
  if UVec.null a
  then []
  else UVec.toList (UVec.findIndices (>0) a)


get_fassigned :: Assignment -> [SVar]
-- return a list of variables assigned to false
get_fassigned a = 
  if UVec.null a
  then []
  else UVec.toList (UVec.findIndices (<0) a)


falselits :: Assignment -> SymbolTable -> [SPVar]
falselits a st = List.map (get_lit st) (get_fassigned a)


trueatoms :: Assignment -> SymbolTable -> [Atom]
trueatoms a st = List.concatMap atomsfromvar (List.map (get_lit st) (get_tassigned a))


falseatoms :: Assignment -> SymbolTable -> [Atom]
falseatoms a st = List.concatMap atomsfromvar (List.map (get_lit st) (get_fassigned a))


nonfalseatoms :: Assignment -> SymbolTable -> [Atom]
nonfalseatoms a st = List.concatMap atomsfromvar (List.map (get_lit st) (UVec.toList (UVec.findIndices (>=0) a)))


