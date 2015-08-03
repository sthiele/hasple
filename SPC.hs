module SPC (
    SPC(..),
    initspc,
    add_source,
    source,
    source_pos,
  ) where

import ASP
import PDG
import SPVar
import qualified Data.Map as Map

type SPC =   (Map.Map Atom SPVar)                                               -- SourcePointerCollection
emptyspc :: SPC
-- returns an empyt SPC
emptyspc = Map.empty

initspc :: [Rule] -> SPC
initspc p =
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
