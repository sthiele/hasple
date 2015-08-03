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


get_scope :: [Rule] -> SPC -> [SPVar] -> Assignment -> [Atom]
get_scope p spc spvars assig =
  let s = collect_nonfalse_cyclic_atoms assig spvars p spc in
  extend_scope p assig spvars spc s 

  
collect_nonfalse_cyclic_atoms :: Assignment -> [SPVar] -> [Rule] -> SPC -> [Atom]
-- return the atoms which have a positive cyclic dependency on themself and are not assigned as False
collect_nonfalse_cyclic_atoms a spvars p spc =
  let non_false_atoms = nonfalseatoms a spvars  in
  [ atom | atom <- non_false_atoms, elem (source atom spc) (BLit [PAtom __conflict]:falselits a spvars) ]


extend_scope :: [Rule] -> Assignment -> [SPVar] -> SPC -> [Atom]  -> [Atom]
-- extend the scope s with atoms that depend on s until a fixpoint is reached
extend_scope p a spvars spc s =
  let
    temp = (nonfalseatoms a spvars) \\ s                    -- remaining nonfalse atoms not in s
    t    = [ atom | atom <- temp, (intersect (source_pos atom spc) (intersect (scc atom (pos_dep_graph p)) s)) /= [] ]
  in
  if null t
  then s
  else extend_scope p a spvars spc (s++t)


unfounded_set :: [Rule] -> Assignment -> [SPVar] -> [Atom]
-- returns an unfounded set for the program given a partial assignment
unfounded_set p a spvars=
  let 
      spc = initspc p
      g   = pos_dep_graph p
      s   = get_scope p spc spvars a 
  in
  loop_s p spc a spvars s


loop_s :: [Rule] -> SPC -> Assignment -> [SPVar] ->[Atom] -> [Atom]

loop_s _ _ _ _ [] = []                                             -- no unfounded_set

loop_s prg spc a spvars s =
  let u                  = head s
      eb                 = bodies2vars (external_bodies prg [u])
      (spc',s',u',found) = loop_u prg spc a spvars s [u] u
  in
  if found
  then u'
  else loop_s prg spc' a spvars s'


loop_u :: [Rule] -> SPC -> Assignment -> [SPVar] -> [Atom] -> [Atom] -> Atom -> (SPC, [Atom], [Atom], Bool)

loop_u _ spc _ _ s [] p = (spc, s, [], False)

loop_u prg spc a spvars s u p =
  let eb = bodies2vars (external_bodies prg u)
      af = falselits a spvars
  in
  if (intersect eb af)==eb
  then (spc, s, u, True)                                                        -- unfounded set found
  else
    let
      BLit b = head (eb \\ af)
      pb     = atomsfromvar (BLit b)
      scc_p  = scc p (pos_dep_graph prg)
    in
    if null (intersect pb (intersect scc_p s))
    then
      let (spc', remove) = shrink_u prg spc u (BLit b)
          u'             = u \\ remove
          s'             = s \\ remove
      in
      loop_u prg spc' a spvars s' u' p
    else
      let u' = u ++ (intersect pb (intersect scc_p s)) in
      loop_u prg spc a spvars s u' p


shrink_u :: [Rule] -> SPC -> [Atom] ->  SPVar -> (SPC, [Atom])
-- returns an updated spc and a list of atoms to be removed from U and S
shrink_u prg spc [] l = (spc,[])

shrink_u prg spc (q:qs) l =
  if elem l (bodies2vars (bodies prg q))
  then
    let (spcn,remove) = shrink_u prg spc qs l in
    (add_source spcn q l, (q:remove))
  else shrink_u prg spc qs l

