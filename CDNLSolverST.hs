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

module CDNLSolverST (
   anssets
) where

import Prelude
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
import STTest
import UFS
import Data.List (head, map, sort, nub, intersect, (\\), delete, null )
import qualified Data.Vector as Vector
import qualified Data.Vector.Unboxed as UVector

import Control.Monad.ST
import Data.STRef

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


transforms :: [CClause] -> SymbolTable -> [Clause]
transforms cclauses st = map (fromCClause st) cclauses


-- -----------------------------------------------------------------------------

-- Conflict Driven Nogood Learning - Enumeration


data TSolver s = TSolver { 
       program                  :: [Rule]          -- the program
     , symboltable              :: SymbolTable     --
     , boocons                  :: Store s         -- the store of boolean constraints
     , decision_level           :: Int             -- the decision level
     , blocked_level            :: Int             -- the blocked level
     , assignment_level         :: Int             -- the assignment level
     , assignment               :: Assignment      -- an assignment
     , dltracker                :: DLT             -- the decision level tracker
     , get_unfounded_set        :: [Atom]          -- unfounded atoms
     , conf                     :: Bool            -- is the state of the solver in conflict
     }

set_program :: [Rule] -> TSolver s -> TSolver s
set_program p            (TSolver _ st ngs dl bl al a dlt u c) = (TSolver p st ngs dl bl al a dlt u c)
--set_symboltable st       (TSolver p _  ngs dl bl al a dlt u c) = (TSolver p st ngs dl bl al a dlt u c)
set_boocons ngs          (TSolver p st _   dl bl al a dlt u c) = (TSolver p st ngs dl bl al a dlt u c)
set_decision_level dl    (TSolver p st ngs _  bl al a dlt u c) = (TSolver p st ngs dl bl al a dlt u c)
set_blocked_level bl     (TSolver p st ngs dl _  al a dlt u c) = (TSolver p st ngs dl bl al a dlt u c)
set_assignment_level al  (TSolver p st ngs dl bl _  a dlt u c) = (TSolver p st ngs dl bl al a dlt u c)
set_assignment a         (TSolver p st ngs dl bl al _ dlt u c) = (TSolver p st ngs dl bl al a dlt u c)
set_dltracker dlt        (TSolver p st ngs dl bl al a _   u c) = (TSolver p st ngs dl bl al a dlt u c)
set_unfounded_set u      (TSolver p st ngs dl bl al a dlt _ c) = (TSolver p st ngs dl bl al a dlt u c)
set_conf c               (TSolver p st ngs dl bl al a dlt u _) = (TSolver p st ngs dl bl al a dlt u c)
 

mkSolver :: [Rule]         ->
            SymbolTable    ->
            Store s        ->
            Int            ->
            Int            ->
            Int            ->
            Assignment     ->
            DLT            ->
            [Atom]         ->
            Bool           -> ST s (TSolver s)
mkSolver prg st ngs dl bl al a dlt u conf  =
  do
    return $ (TSolver prg st (ngs) dl bl al a dlt u conf)

 
anssets :: [Rule] -> [[Atom]]
-- create a solver and initiate solving process
anssets prg  =
  let s      = 0
      cngs   = nub (nogoods_of_lp prg)
      st     = Vector.fromList (get_vars cngs)
      png    = transforms cngs st
      l      = Vector.length st
      dl     = 1
      bl     = 1
      al     = 1
      a      = initAssignment l
      dlt    = []
      u      = []
      conf   = False
--       solver = TSolver prg st ngs dl bl al a dlt u conf
  in
--   trace ("Clauses: " ++ (show png)) $
--   trace ("SymbTab: " ++ (show st)) $
  runST $ do
    ngs <- mkStore png
    solver <- mkSolver prg st ngs dl bl al a dlt u conf
    cdnl_enum solver s

-- TODO preprocessing
-- simplifyCNF [] = []
-- simplifyCNF x = simplifyCNF' x [] []
-- simplicyCNF' (x:xs) t f =
--   case x of 
--     (UClause c) -> simplifyCNF xs
--     _ -> (x:(simplifyCNF xs t f))


-- get_occurence_list
traceMonad :: (Show a, Monad m) => a -> m a
traceMonad x = trace (show x) (return x)

cdnl_enum :: TSolver s -> Int -> ST s [[Atom]]
cdnl_enum solver s =
  let
    solverp = set_unfounded_set [] solver 
  in
  do
    solver' <- nogood_propagation solverp
--     traceMonad ("cdnl: " ++ (show (assignment solver')))
    if conf solver'
    then                                                                                                 -- conflict
      if (decision_level solver') == 1
      then return $ []                                         -- no need for conflict handling, no more answer sets
      else                                                                                      -- conflict handling
        do
--           traceMonad ("cdnl: conflict detected")
          solver'' <- conflict_handling solver'
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
        then return $ [nub (trueatoms a' (symboltable solver'))]                                  -- last answer set
        else                                                                  -- backtrack for remaining answer sets
          let
              dl           = decision_level solver'
              sigma_d      = get_dliteral dlt dl
              cal          = dl2al dlt dl
              dlt'         = dlbacktrack dlt dl
              a''          = backtrack a' cal
              a'''         = assign a'' (invert sigma_d) cal                         -- invert last decision literal
              solver''     = set_decision_level           (dl-1) $
                             set_blocked_level            (dl-1) $
                             set_dltracker                  dlt' $
                             set_assignment_level        (cal+1) $
                             set_assignment a'''           solver'
          in
          do
            remaining_as <- cdnl_enum solver'' (s-1)
            return $ (nub (trueatoms a' (symboltable solver'))):remaining_as
      else                                                                                         -- select new lit
        let dl          = decision_level solver'
            sigma_d_e   = head selectable
            dlt'_e      = (al',dl+1,(T sigma_d_e)):dlt
            a''_e       = assign a' (T sigma_d_e) al'
            solver''_e  = set_decision_level           (dl+1) $
                          set_dltracker                dlt'_e $
                          set_assignment_level        (al'+1) $
                          set_assignment a''_e          solver'
        in
--         trace ("choose: " ++ (show sigma_d_e)) $
        do cdnl_enum solver''_e s


conflict_handling :: TSolver s -> ST s (TSolver s)
-- should resolve the conflict learn a new maybe clause and backtrack the solver
conflict_handling s =
  let a   = assignment     s
      bl  = blocked_level  s
      dl  = decision_level s
      dlt = dltracker      s
      ngs = boocons        s
  in
  if bl < dl
  then                                                                           -- learn a new nogood and backtrack
    do
      (ngs', sigma_uip, alx) <-  conflict_analysis ngs a dlt
      let bt_dl = al2dl dlt alx                                                                         -- backtrack
      let bt_al = dl2al dlt bt_dl
      let a'    = assign (backtrack a bt_al) (invert sigma_uip) bt_al
      let dlt'  = dlbacktrack dlt bt_dl
      return $ ( set_decision_level   (bt_dl-1) $
                 set_dltracker             dlt' $
                 set_assignment_level (bt_al+1) $
                 set_assignment              a' $
                 set_boocons               ngs' $
                 set_conf                 False s )
  else                                                                                                  -- backtrack
    let 
        sigma_d = get_dliteral dlt dl
        dl'     = dl-1
        bt_al   = dl2al dlt dl'
        a'      = assign (backtrack a bt_al) (invert sigma_d) bt_al
        dlt'    = dlbacktrack dlt dl'
    in
    return $ ( set_decision_level     dl' $
               set_blocked_level      dl' $
               set_dltracker         dlt' $
               set_assignment_level bt_al $
               set_assignment          a' $
               set_conf             False s )
    

conflict_analysis :: NogoodStore s -> Assignment -> DLT -> ST s (NogoodStore s, SignedVar, Int)
conflict_analysis ngs a dlt =
  let conflict_nogood = get_ng ngs
--       ngs'            = rewind ngs
  in
  do
    ngs' <- rewind ngs
    v_conflict_nogood <- readSTRef conflict_nogood
--     traceMonad ("conflict_analysis: " ++ (show a) ++" "++ (show v_conflict_nogood))
    conflict_resolution ngs' v_conflict_nogood a dlt



-- Propagation

tight :: [Rule] -> Bool  -- TODO implement tightness check
-- return true if the program is tight
tight p = False


nogood_propagation :: TSolver s -> ST s (TSolver s)
-- propagate nogoods
nogood_propagation s =
  do
    s' <- local_propagation s
--     traceMonad ("nogo_prop: " ++ (show (assignment s')))
    if conf s'
    then return $ s'
    else
      let
        prg = program           s
        st  = symboltable       s
        u   = get_unfounded_set s
        a   = assignment        s'
        al  = assignment_level  s'
        ngs = boocons           s'
      in
      if tight prg
      then return $ s'
      else
        case ufs_check prg a st u of                                                           -- unfounded set check
          [] -> return $ s'                                                                     -- no unfounded atoms
          u' -> let p = get_svar (ALit (head u')) st in                                            -- unfounded atoms
                if Assignment.elem (T p) a
                then
                  let cngs_of_loop = loop_nogoods prg u'
                      ngs_of_loop  = transforms cngs_of_loop st
--                       s''          = set_boocons ngs' s'
                  in
                  do
                    ngs' <- add_nogoods ngs ngs_of_loop
                    nogood_propagation (set_boocons ngs' s')
                else
                  if Assignment.elem (F p) a
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


local_propagation :: TSolver s -> ST s (TSolver s)
-- itterate over the nogoods and try to resolve them until nothing new can be infered or a conflict is found
local_propagation s =
--   trace ("loc_prop: " ) $
  if conf s
  then return s
  else 
    if can_choose $ boocons s
    then
      do
        s' <- CDNLSolverST.resolve $ choose_next_ng s
--         traceMonad ("loc_prop: " ++ (show (assignment s')))
        local_propagation s'

    else
--       trace ("loc_prop: " ++ "all clauses done") $
--       let ngs' = rewind $ boocons s in -- rewind for next use
      do
        ngs' <- rewind (boocons s)
        return $ set_boocons ngs' s


choose_next_ng :: TSolver s -> TSolver s
choose_next_ng s = set_boocons (choose $ boocons s) s


resolve :: TSolver s -> ST s (TSolver s)
-- resolve the current no good
resolve s =
--   trace ("res: " ) $
  let ng = get_ng (boocons s)
      al = assignment_level s
  in
  do
    v_ng <- readSTRef ng
    res <- STTest.resolve (boocons s) v_ng al (assignment s)

    case (res) of
      NIX         -> return $ s
      Res a'      -> do
                      ngs' <- rewind (boocons s)
                      return $ set_boocons (ngs') $ set_assignment_level (al+1) $ set_assignment a' s
      CONF        -> return $ (set_conf True s)




