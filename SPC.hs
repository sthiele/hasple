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

module SPC (
    SPC(..),
    fromProgram,
    add_source,
    source,
    source_pos,
  ) where

import ASP
import PDG
import SPVar
import qualified Data.Map as Map

type SPC = (Map.Map Atom SPVar)                                               -- SourcePointerCollection


fromProgram :: [Rule] -> SPC
-- create a source pointer collection from a program
fromProgram p =
  let atoms = atoms_p p
      g     = pos_dep_graph p
      spc   = Map.empty
  in
  init_sources spc g atoms


init_sources :: SPC -> PDG -> [Atom] -> SPC
init_sources spc g [] = spc
init_sources spc g (a:as) =
  if cyclic a g
  then
    let spc' = Map.insert a (BLit [PAtom __conflict]) spc in
    init_sources spc' g as
  else init_sources spc g as

  
add_source ::  SPC -> Atom -> SPVar -> SPC
-- add a new source for an atom a
add_source spc a l = Map.insert a l spc


source_pos :: Atom -> SPC -> [Atom]
-- get the sources of a
source_pos a spc =
  case Map.lookup a spc of
    Nothing       -> []
    Just (BLit b) -> [ a | PAtom a <- b ] -- maybe special case of __conflict


source :: Atom -> SPC -> SPVar
-- get the sources of a
source a spc =
  case Map.lookup a spc of
    Nothing -> BLit []
    Just x  -> x


