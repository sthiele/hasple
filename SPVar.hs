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
) where
       
import ASP
import Data.List (nub, delete, intersect)
-- import Debug.Trace


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

get_vars cs = nub (concatMap get_varsc cs)

get_varsc :: CClause -> [SPVar]

get_varsc (t,f) = nub (t ++ f)


nogoods_of_lp :: [Rule] -> [CClause]

nogoods_of_lp p =
  let a   = (atoms_p p)++[__conflict]
      b   = bodies_p p
      ng1 = map get_ng1 b           -- body is true if all lits of it are true -- not ( body=false and all lits=true)
      ng2 = concatMap get_ng2 b     -- body is true if all lits of it are true -- not ( body=true and one lit=false)
      ng3 = concatMap (get_ng3 p) a -- a head is true if one body is true -- not ( head=false and one body=true)
      ng4 = map (get_ng4 p) a       -- a head is true if one body is true -- not ( head=true and all bodies=false)
      ngx = [([__bottom],[])]       -- no conflict literal
  in
  ng1++ng2++ng3++ng4++ngx


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
  clauses1 ++ clauses2


get_ng3 :: [Rule] -> Atom -> [CClause]

get_ng3 p a = [ ([BLit b], [ALit a]) | b <- (bodies p a) ]


get_ng4 :: [Rule] -> Atom -> CClause

get_ng4 p a = ([ALit a], bodies2vars (bodies p a))


external_bodies :: [Rule] -> [Atom] -> [[Literal]]
-- returns the external bodies
external_bodies p u =
  [ body r |  r <- p, elem (kopf r) u, null (intersect (pbody r) u) ]


loop_nogood :: Atom -> [[Literal]] -> CClause
-- returns the loop nogood for an atom in an unfounded set(characterized by the external bodies)
loop_nogood a bodies = ([ALit a], bodies2vars bodies)


loop_nogoods :: [Rule] -> [Atom] -> [CClause]
-- return the loop nogoods of the program for a given unfounded set
loop_nogoods p u = [ loop_nogood atom (external_bodies p u) | atom<-u ]

