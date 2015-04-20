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
   Assignment(..),
   AssignedVar(..),
   SVar(..),
   assign,
   unsign,
   invert,
   elemAss,
   isassigned
  ) where
import ASP   
type SVar = Int


-- data AssignedVar = T SVar
--          | F SVar
--          deriving (Show,Eq,Ord)
         
-- playing with new representation
data AssignedVar = T Int
         | F Int
         deriving (Show,Eq,Ord)

unsign:: AssignedVar -> SVar
unsign (T l) = l
unsign (F l) = l

invert:: AssignedVar -> AssignedVar
invert (T l) = (F l)
invert (F l) = (T l)


type Assi = [Integer]

assign a (T l) = (take (l-1) a) ++ [1] ++ (drop l a)
assign a (F l) = (take (l-1) a) ++ [-1] ++ (drop l a)         

-- type Assignment = ([SVar],[SVar])
type Assignment = Assi

elemAss:: AssignedVar -> Assignment -> Bool
-- returns true if the assignment contains the AssignedVar
-- elemAss (T l) (t,_) = elem l t
-- elemAss (F l) (_,f) = elem l f
elemAss (T l) a = (head (drop (l-1) a))==1
elemAss (F l) a = (head (drop (l-1) a))==(-1)

isassigned:: SVar -> Assignment -> Bool
isassigned l a = (head (drop (l-1) a))/=0
