module PDG (
    PDG(..),
    pos_dep_graph,
    cyclic,
    scc,
  ) where

import ASP
import Data.List ((\\))
import qualified Data.Map as Map


type PDG = (Map.Map Atom [Atom])                                                -- PositiveDependencyGraph

pos_dep_graph :: [Rule] -> PDG
-- create a pdg for a program
pos_dep_graph prg = pos_dep_graph2 prg Map.empty

pos_dep_graph2 [] accu = accu

pos_dep_graph2 (r:rs) accu =
  let h  = kopf r
      pb = pbody r
  in
  case Map.lookup h accu of
    Nothing -> let naccu = Map.insert h pb accu in
               pos_dep_graph2 rs naccu
    Just x  -> let naccu = Map.insert h (pb++x) accu in
               pos_dep_graph2 rs naccu


scc :: Atom -> PDG -> [Atom]
-- returns the strongly connected component of an atom
scc a depg = tarjan depg [] [] a


tarjan :: PDG -> [Atom] -> [Atom] -> Atom -> [Atom]
-- given a dependency graph compute the scc of an atom a
tarjan depg visited visited2 a  =
   if elem a visited
   then
     case Map.lookup a depg of
       Nothing -> (a:visited2)
       Just x  -> let next = x \\ visited2 in
                  if null next
                  then (a:visited2)
                  else concatMap (tarjan depg visited (a:visited2)) next
   else
     case Map.lookup a depg of
       Nothing -> visited2
       Just x  -> let next = x \\ visited2 in
                  if null next
                  then visited2
                  else concatMap (tarjan depg (a:visited) visited2) next


cyclic:: Atom -> PDG -> Bool
-- test if an atom has a cyclic definition might be easier, if scc\=[]
cyclic a g =
  let scc_a = scc a g in
  not (null scc_a)
