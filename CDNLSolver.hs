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

module CDNLSolver (
   anssets
) where

import Prelude (($), (+), (-), (++))
import Data.Bool
import Data.Int
import Data.Eq
import Data.Ord
import Text.Show
import ASP
import SPVar
import Assignment (Assignment, initAssignment, unassigned, trueatoms, elem, assign, backtrack)
import SPC
import DLT
import qualified NGS
import UFS
import Data.List (head, map, sort, nub, intersect, (\\), delete, null )
import qualified Data.Vector as Vector
import qualified Data.Vector.Unboxed as UVector

import Data.Maybe
import qualified Data.Map as Map
import Debug.Trace


------------------------------
-- little helper

get_svar :: SPVar -> SymbolTable -> SVar
get_svar l st = get_svar2 l st 0

get_svar2 :: SPVar -> SymbolTable -> Int -> SVar
get_svar2 s st i =
  if st Vector.!i == s 
    then i
      else get_svar2 s st (i+1)


transforms :: [CClause] -> SymbolTable -> [NGS.Clause]
transforms cclauses st = map (NGS.fromCClause st) cclauses


-- -----------------------------------------------------------------------------

-- Conflict Driven Nogood Learning - Enumeration


data TSolver = TSolver { 
                         program                  :: [Rule]          -- the program
                       , is_tight                 :: Bool
                       , symboltable              :: SymbolTable     --
                       , boocons                  :: NGS.NogoodStore -- the store of boolean constraints
                       , decision_level           :: Int             -- the decision level 
                       , blocked_level            :: Int             -- the blocked level
                       , assignment_level         :: Int             -- the assignment level
                       , assignment               :: Assignment      -- an assignment
                       , dltracker                :: DLT             -- the decision level tracker
                       , get_unfounded_set        :: [Atom]          -- unfounded atoms
                       , conf                     :: Bool            -- is the state of the solver in conflict
                       } deriving (Show, Eq)

set_program :: [Rule] -> TSolver -> TSolver
set_program p                    (TSolver _ t st ngs dl bl al a dlt u c) = (TSolver p t st ngs dl bl al a dlt u c)
set_symboltable st               (TSolver p t _  ngs dl bl al a dlt u c) = (TSolver p t st ngs dl bl al a dlt u c)
set_boocons ngs                  (TSolver p t st _   dl bl al a dlt u c) = (TSolver p t st ngs dl bl al a dlt u c)
set_decision_level dl            (TSolver p t st ngs _  bl al a dlt u c) = (TSolver p t st ngs dl bl al a dlt u c)
set_blocked_level bl             (TSolver p t st ngs dl _  al a dlt u c) = (TSolver p t st ngs dl bl al a dlt u c)
set_assignment_level al          (TSolver p t st ngs dl bl _  a dlt u c) = (TSolver p t st ngs dl bl al a dlt u c)
set_assignment a                 (TSolver p t st ngs dl bl al _ dlt u c) = (TSolver p t st ngs dl bl al a dlt u c)
set_dltracker dlt                (TSolver p t st ngs dl bl al a _   u c) = (TSolver p t st ngs dl bl al a dlt u c)
set_unfounded_set u              (TSolver p t st ngs dl bl al a dlt _ c) = (TSolver p t st ngs dl bl al a dlt u c)
set_conf c                       (TSolver p t st ngs dl bl al a dlt u _) = (TSolver p t st ngs dl bl al a dlt u c) 
 

anssets :: [Rule] -> [[Atom]]
-- create a solver and initiate solving process
anssets prg  =
  let t      = tight prg
      cngs   = nub (nogoods_of_lp prg)
      st     = Vector.fromList (get_vars cngs)
      png    = transforms cngs st
      ngs    = NGS.new_ngs png []
      l      = Vector.length st
      dl     = 1
      bl     = 1
      al     = 1
      a      = initAssignment l
      dlt    = []
      u      = []
      conf   = False
      solver = TSolver prg t st ngs dl bl al a dlt u conf
  in
--   trace ("Clauses: " Prelude.++ (show png)) $
--   trace ("SymbTab: " Prelude.++ (show st)) $  
  cdnl_enum solver 0


cdnl_enum :: TSolver -> Int -> [[Atom]]
cdnl_enum solver s =
  let
    solverp = set_unfounded_set [] solver 
    solver' = nogood_propagation solverp
  in
--   trace ("cdnl: " Prelude.++ (show (assignment solver'))) $
  if conf solver'
  then                                                                                                 -- conflict
    if (decision_level solver') == 1
    then []                                                  -- no need for conflict handling, no more answer sets
    else                                                                                      -- conflict handling
      let solver'' = conflict_handling solver' in
      cdnl_enum solver'' s
  else                                                                                              -- no conflict
    let 
      a'         = assignment       solver'
      al'        = assignment_level solver'
      dlt        = dltracker        solver'
      selectable = unassigned a' 
    in
    if null selectable
    then                                                                     -- if all atoms then answer set found
      if (decision_level solver')==1 || s==1
      then [nub (trueatoms a' (symboltable solver'))]                                           -- last answer set
      else                                                                  -- backtrack for remaining answer sets
        let dl           = decision_level solver'
            sigma_d      = get_dliteral dlt dl
            cal          = dl2al dlt dl
            dlt'         = dlbacktrack dlt dl
            a''          = backtrack a' cal
            a'''         = assign a'' (invert sigma_d) cal                         -- invert last decision literal
            solver''     = set_decision_level         (dl-1) $
                           set_blocked_level          (dl-1) $
                           set_dltracker                dlt' $
                           set_assignment_level      (cal+1) $ 
                           set_assignment a'''         solver'
            remaining_as = cdnl_enum solver'' (s-1)
        in
        (nub (trueatoms a' (symboltable solver'))):remaining_as
    else                                                                                         -- select new lit
      let dl           = decision_level solver'
          sigma_d      = head selectable
          dlt'         = (al',dl+1,(T sigma_d)):dlt
          a''          = assign a' (T sigma_d) al'
          solver''     = set_decision_level         (dl+1) $
                         set_dltracker                dlt' $
                         set_assignment_level      (al'+1) $
                         set_assignment a''          solver'
          remaining_as = cdnl_enum solver'' s
      in
--       trace ("choose: " Prelude.++ (show sigma_d)) $
      remaining_as


conflict_handling :: TSolver -> TSolver
-- should resolve the conflict learn a new maybe clause and backtrack the solver
conflict_handling s =
  let a   = assignment     s
      bl  = blocked_level  s
      dl  = decision_level s
      dlt = dltracker      s
  in
  if bl < dl
  then                                                                         -- learn a new nogood and backtrack
    let ngs                    = boocons s 
        (ngs', sigma_uip, alx) = conflict_analysis ngs a dlt
    in
    let                                                                                               -- backtrack
        bt_dl = al2dl dlt alx
        bt_al = dl2al dlt bt_dl
        a'    = assign (backtrack a bt_al) (invert sigma_uip) bt_al
        dlt'  = dlbacktrack dlt bt_dl
    in 
    set_decision_level   (bt_dl-1) $
    set_dltracker             dlt' $
    set_assignment_level (bt_al+1) $ 
    set_assignment              a' $ 
    set_boocons               ngs' $               
    set_conf                 False s 
  else                                                                                                -- backtrack
    let 
        sigma_d = get_dliteral dlt dl
        dl'     = dl-1
        bt_al   = dl2al dlt dl'
        a'      = assign (backtrack a bt_al) (invert sigma_d) bt_al
        dlt'    = dlbacktrack dlt dl'
    in
    set_decision_level     dl' $
    set_blocked_level      dl' $
    set_dltracker         dlt' $
    set_assignment_level bt_al $ 
    set_assignment          a' $              
    set_conf             False s
    

conflict_analysis :: NGS.NogoodStore -> Assignment -> DLT -> (NGS.NogoodStore, SignedVar, Int)
conflict_analysis ngs a dlt =
  let conflict_nogood = NGS.get_ng ngs
      ngs'            = NGS.rewind ngs
  in
  NGS.conflict_resolution ngs' conflict_nogood a dlt



-- Propagation


nogood_propagation :: TSolver -> TSolver
-- propagate nogoods
nogood_propagation s =
  let
    prg = program           s 
    st  = symboltable       s
    u   = get_unfounded_set s 
    s'  = local_propagation s
    a   = assignment        s'
    al  = assignment_level  s'
    ngs = boocons           s'
  in
--   trace ("nogo_prop: " Prelude.++ (show (assignment s'))) $
  if conf s'
  then s'
  else
    if is_tight s
    then s'
    else
      case ufs_check prg a st u of                                                           -- unfounded set check
        [] -> s'                                                                              -- no unfounded atoms
        u' -> let p = get_svar (ALit (head u')) st in                                            -- unfounded atoms
              if elem (T p) a
              then
                let cngs_of_loop = loop_nogoods prg u'
                    ngs_of_loop  = transforms cngs_of_loop st
                    ngs'         = NGS.add_nogoods ngs_of_loop ngs
                    s''          = set_boocons ngs' s'
                in
                nogood_propagation s''
              else
                if elem (F p) a
                then
                  let s'' = set_unfounded_set u' s' in
                  nogood_propagation s''
                else
                  let a'  = assign a (F p) al                                                  -- extend assignment
                      s'' = set_assignment_level (al+1) $ 
                            set_assignment a'           $ 
                            set_unfounded_set u'       s'
                  in
                  nogood_propagation s''


local_propagation :: TSolver -> TSolver
-- itterate over the nogoods and try to resolve them until nothing new can be infered or a conflict is found
local_propagation s =
  if conf s
  then s
  else 
    if NGS.can_choose $ boocons s
    then
      let a = choose_next_ng    s
          b = resolve a
      in
--       trace ("loc_prop: " Prelude.++ (show (assignment b))) $
      let
          c = local_propagation b
      in
      c
--       local_propagation $  resolve  $  choose_next_ng    s
    else
--       trace ("loc_prop: " Prelude.++ "no choice") $
      let ngs' = NGS.rewind $ boocons s in -- rewind for next use
      set_boocons ngs' s


choose_next_ng :: TSolver -> TSolver
choose_next_ng s = set_boocons (NGS.choose $ boocons s) s


resolve :: TSolver -> TSolver
-- resolve the current no good
resolve s =
    let al = (assignment_level s)
        ng = NGS.get_ng (boocons s)
        x  = NGS.resolve al ng (assignment s)
    in
--    trace ("res: " ++ (show x)) $
    case x of
      NGS.NIX         -> s
      NGS.NIXU ng'    -> let ngs' = NGS.upgrade (boocons s) ng' in
                         set_boocons ngs' s
      NGS.Res a'      -> let ngs' = NGS.rewind (boocons s) in
                         set_boocons ngs' $ set_assignment_level (al+1) $ set_assignment a' s
      NGS.ResU a' ng' -> let ngs' = NGS.up_rew (boocons s) ng' in
                         set_boocons ngs' $ set_assignment_level (al+1) $ set_assignment a' s
      NGS.CONF        -> set_conf True s                                                               -- set conflict


