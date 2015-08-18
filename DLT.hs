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

module DLT (
  DLT,
  al2dl,
  dl2al,
  get_dliteral,
  dlbacktrack,
) where

import Types


type DLT = [(Int, Int, SignedVar)]                                                   -- DLT
-- maps assignment level to decision level and decision literal

get_dliteral :: DLT  -> Int -> SignedVar
-- return the decision literal at a level
get_dliteral ((al1,dl1,sl1):xs) l
  | dl1 == l = sl1
  | otherwise = get_dliteral xs l

  
dlbacktrack :: DLT  -> Int -> DLT 
-- backtracks to a decision level
dlbacktrack ((al1,dl1,sl1):xs) l =
  if dl1 < l
  then ((al1,dl1,sl1):xs)
  else dlbacktrack xs l

  
al2dl :: DLT -> Int -> Int
al2dl ((al1,dl1,sl1):rest) al =
  if al<al1
  then al2dl rest al
  else dl1

  
dl2al :: DLT -> Int -> Int
dl2al ((al1,dl1,sl1):rest) dl =
  if dl==dl1
  then al1
  else dl2al rest dl

