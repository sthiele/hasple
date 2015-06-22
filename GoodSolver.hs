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

module GoodSolver (
   anssets,
   reduct,
   facts,
  ) where

import ASP
import Data.List (sort, nub, intersect, (\\) )


subsets:: [a] -> [[a]]
subsets []  = [[]]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)


facts:: [Rule] -> [Atom]
-- return the facts of a programm
facts p = [ (kopf r) |  r <- p,  (null (pbody r)), (null (nbody r)) ]


reducebasicprogram:: [Rule] -> [Atom] -> [Rule]
-- reduces a program by  aset of atoms
reducebasicprogram p x = [ (basicRule (kopf r) ((pbody r)\\ x) ) | r <- p, (pbody r)/=[] ]


cn:: [Rule] -> [Atom]
-- return the consequences of a  basic logic programm
cn [] = []

cn p =
   if (reducebasicprogram p (facts p)) == p
   then (facts p)
   else nub ((facts p) ++ (cn (reducebasicprogram p (facts p))))


reduct:: [Rule] -> [Atom] -> [Rule]
-- return the reduct of a logic program with x
reduct p x = [ (basicRule (kopf r) (pbody r)) |  r <- p,  (intersect (nbody r) x)==[] ]


anssets:: [Rule] -> [[Atom]]

anssets p = filter (\i -> (sort (cn (reduct p i)))==(sort i)) (subsets (heads_p p))