-- Copyright (c) 2015, Sven Thiele <sthiele78@gmail.com>
--
-- -- This file is part of hasple.
--
-- -- hasple is free software: you can redistribute it and/or modify
-- -- it under the terms of the GNU General Public License as published by
-- -- the Free Software Foundation, either version 3 of the License, or
-- -- (at your option) any later version.
--
-- -- hasple is distributed in the hope that it will be useful,
-- -- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- -- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- -- GNU General Public License for more details.
--
-- -- You should have received a copy of the GNU General Public License
-- -- along with hasple.  If not, see <http://www.gnu.org/licenses/>.

module SPVar (
  SPVar(..),
--    __bottom,
  bodies2vars,
  atomsfromvar,
  bodies,
  external_bodies,
  get_vars,
  CClause,
  nogoods_of_lp,
  loop_nogoods,
  SVar,
  SignedVar(..),
  unsign,
  invert,
  SymbolTable,
  get_lit
) where
       
import ASP
import Data.List (nub, delete, intersect, (++), map)
import Data.Vector as BVec


data SPVar = ALit Atom                                                          -- Solver-Variable
           | BLit [Literal]
           deriving (Show,Eq,Ord)

__bottom :: SPVar
-- returns the of Solver-variable representing a conflict
__bottom = ALit __conflict


atoms2vars :: [Atom] -> [SPVar]
-- returns a list of Solver-variables
atoms2vars as = [ ALit a | a <- as ]


bodies2vars :: [[Literal]] -> [SPVar]
-- returns a list of Solver-variables
bodies2vars bs = [ BLit b | b <- bs ]


atomsfromvar :: SPVar -> [Atom]
-- 
atomsfromvar (ALit a) = [a]
atomsfromvar (BLit b) = [ a | PAtom a <- b]


bodies_p :: [Rule] -> [[Literal]]
-- returns all bodies of a program
bodies_p p = [ body r | r <-p ]

bodies :: [Rule] -> Atom -> [[Literal]]
-- returns all bodies of rules with the atom as head
bodies p a  = [ body r | r<-p , (kopf r)==a ]

-- ---------------------------------------------------------------------------------

type CClause = ([SPVar],[SPVar])


get_vars :: [CClause] -> [SPVar]
get_vars cs = nub (Prelude.concatMap get_varsc cs)

get_varsc :: CClause -> [SPVar]
get_varsc (t,f) = nub (t Prelude.++ f)


nogoods_of_lp :: [Rule] -> [CClause]
nogoods_of_lp p =
  let a   = (atoms_p p)Prelude.++[__conflict]
      b   = bodies_p p
      ng1 = Prelude.map get_ng1 b           -- body is true if all lits of it are true -- not ( body=false and all lits=true)
      ng2 = Prelude.concatMap get_ng2 b     -- body is true if all lits of it are true -- not ( body=true and one lit=false)
      ng3 = Prelude.concatMap (get_ng3 p) a -- a head is true if one body is true -- not ( head=false and one body=true)
      ng4 = Prelude.map (get_ng4 p) a       -- a head is true if one body is true -- not ( head=true and all bodies=false)
      ngx = [([__bottom],[])]       -- no conflict literal
  in
  ng1 Prelude.++ ng2 Prelude.++ ng3 Prelude.++ ng4 Prelude.++ ngx


get_ng1 :: [Literal] -> CClause
get_ng1 b =
  let pb = [ a | PAtom a <- b ]
      nb = [ a | NAtom a <- b ]
  in
  ((atoms2vars pb), ((BLit b):(atoms2vars nb)))


get_ng2 :: [Literal] -> [CClause]
get_ng2 b =
  let
    pb       = [ a | PAtom a <- b ]
    nb       = [ a | NAtom a <- b ]
    clauses1 = [ ([BLit b], [ALit atom]) | atom <- pb ]
    clauses2 = [ ([BLit b, ALit atom],[]) | atom <- nb ]
  in
  clauses1 Prelude.++ clauses2


get_ng3 :: [Rule] -> Atom -> [CClause]
get_ng3 p a = [ ([BLit b], [ALit a]) | b <- (bodies p a) ]


get_ng4 :: [Rule] -> Atom -> CClause
get_ng4 p a = ([ALit a], bodies2vars (bodies p a))


external_bodies :: [Rule] -> [Atom] -> [[Literal]]
-- returns the external bodies
external_bodies p u =
  [ body r |  r <- p, Prelude.elem (kopf r) u, Prelude.null (intersect (pbody r) u) ]


loop_nogood :: Atom -> [[Literal]] -> CClause
-- returns the loop nogood for an atom in an unfounded set(characterized by the external bodies)
loop_nogood a bodies = ([ALit a], bodies2vars bodies)


loop_nogoods :: [Rule] -> [Atom] -> [CClause]
-- return the loop nogoods of the program for a given unfounded set
loop_nogoods p u = [ loop_nogood atom (external_bodies p u) | atom<-u ]



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

get_lit :: SymbolTable -> SVar -> SPVar
get_lit st i = st BVec.! i


