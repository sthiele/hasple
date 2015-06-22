module UFS (
    unfounded_set,
  ) where

import ASP
import SPVar
import PDG
import SPC
import Types
import Data.List (nub, intersect, (\\))

-- import Debug.Trace



data Stuff = Stuff { prg :: [Rule],
                     gra :: PDG,
                     spc :: SPC,
                     ass :: Assignment,
                     dict:: [SPVar]
}


get_scope :: [Rule] -> SPC -> [SPVar] -> Assignment -> [Atom]
get_scope p spc spvars assig =
  let s = collect_nonfalse_cyclic_atoms assig spvars p spc in
  extend_scope p assig spvars spc s 

  
collect_nonfalse_cyclic_atoms:: Assignment -> [SPVar] -> [Rule] -> SPC -> [Atom]
-- return the atoms which have a positive cyclic dependency on themself and are not assigned as False
collect_nonfalse_cyclic_atoms assig spvars p spc =
--   let non_false_atoms = nub (atoms_p p) \\ (falseatoms assig spvars)  in
  let non_false_atoms = nonfalseatoms assig spvars  in
  [ a | a <- non_false_atoms, elem (source a spc) ((BLit [PAtom __conflict]):(falselits assig spvars)) ]


extend_scope:: [Rule] -> Assignment -> [SPVar] -> SPC -> [Atom]  -> [Atom]
-- extend the scope s with atoms that depend on s until a fixpoint is reached
extend_scope p assig spvars spc s =
  let
--     temp = nub (atoms_p p) \\ ((falseatoms assig spvars)++s) -- remaining nonfalse atoms not in s
    temp = (nonfalseatoms assig spvars) \\ s                    -- remaining nonfalse atoms not in s
    t =[ a | a <- temp, (intersect (source_pos a spc) (intersect (scc a (pos_dep_graph p)) s)) /= [] ]
  in
  if null t
  then s
  else extend_scope p assig spvars spc (s++t)


unfounded_set:: [Rule] -> SPC -> Assignment -> [SPVar] -> [Atom]
-- returns an unfounded set for the program given a partial assignment
unfounded_set p spc assig spvars=
  let g = pos_dep_graph p
      s = get_scope p spc spvars assig in
--   mtrace ( "unfounded_set: s:" ++ (show s)) $
  loop_s p spc assig spvars s


loop_s:: [Rule] -> SPC -> Assignment -> [SPVar] ->[Atom] -> [Atom]

loop_s prg spc assig spvars [] = []                                             -- no unfounded_set

loop_s prg spc assig spvars s =
  let u = head s
      eb = bodies2vars (external_bodies prg [u])
      (spc2,s2,u2,found) = loop_u prg spc assig spvars s [u] u
  in
  if found
  then u2
  else loop_s prg spc2 assig spvars s2


loop_u:: [Rule] -> SPC -> Assignment -> [SPVar] -> [Atom] -> [Atom] -> Atom -> (SPC, [Atom], [Atom], Bool)

loop_u prg spc assig spvars s [] p = (spc, s, [], False)

loop_u prg spc assig spvars s u p =
  let eb = bodies2vars (external_bodies prg u)
      af = falselits assig spvars
  in
  if (intersect eb af)==eb
  then (spc, s, u, True)                                                        -- unfounded set found
  else
    let
      (BLit b) = (head (eb \\ af))
      pb = atomsfromvar (BLit b)
      scc_p = scc p (pos_dep_graph prg)
    in
    if null (intersect pb (intersect scc_p s))
    then
      let (spc2, remove) = shrink_u prg spc u (BLit b)
          u2 = u \\ remove
          s2 = s \\ remove
      in
      loop_u prg spc2 assig spvars s2 u2 p
    else
      let u2 = u ++ (intersect pb (intersect scc_p s)) in
      loop_u prg spc assig spvars s u2 p


shrink_u:: [Rule] -> SPC -> [Atom] ->  SPVar -> (SPC, [Atom])
-- returns an updated spc and a list of atoms to be removed from U and S
shrink_u prg spc [] l = (spc,[])

shrink_u prg spc (q:qs) l =
  if elem l (bodies2vars (bodies prg q))
  then
    let (spcn,remove) = shrink_u prg spc qs l in
    ((add_source spcn q l), (q:remove))
  else shrink_u prg spc qs l