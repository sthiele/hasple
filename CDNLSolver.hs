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
   cdnl_enum,
) where

import ASP
import SPVar
import Types
import SPC
import UFS
import Data.List (sort, nub, intersect, (\\), delete )
import Data.Maybe
-- import Data.List.Extra (nubOrd)
-- use sort to order list nub (nubOrd) to remove duplicates from list -- maybe use Sets instead?
import qualified Data.Map as Map
import Debug.Trace


choose :: TSolver -> TSolver
choose s =
  if conf s
  then s
  else set_boocons (choose2 $ boocons s) s



canchoose :: NoGoodStore -> Bool
-- returns true if not all nogoods have been tested
canchoose (NoGoodStore png lng pnga lnga counter) = (counter+1) < (length png) + (length lng) 

choose2 :: NoGoodStore -> NoGoodStore
-- is only called if canchoose return true
choose2 (NoGoodStore png lng pnga lnga counter) = (NoGoodStore png lng pnga lnga (counter+1))


resolv :: TSolver -> TSolver
-- is only called if conf is false
resolv s =
    let al = (assignment_level s)
        ng = get_ng (boocons s)
        x  = resolve al ng (assignment s)
    in
    case x of
      NIX         -> s

      NIXU ng'    -> let ngs' = upgrade_ngs (boocons s) ng' in
                     set_boocons ngs' s
                                                                                                                     
      Res a'      -> let ngs' = rewind (boocons s) in
                     set_boocons ngs' $ set_assignment_level (al+1) $ set_assignment a' s

      ResU a' ng' -> let ngs' = up_rew_ngs (boocons s) ng' in
                     set_boocons ngs' $ set_assignment_level (al+1) $ set_assignment a' s
                                                                                                                     
      CONF        -> set_conf True s   -- set conflict



local_propagation :: TSolver -> TSolver
local_propagation s =
  if conf s
  then s
  else 
    if canchoose (boocons s)
    then local_propagation $ resolv $ choose s
    else 
      let ngs' = rewind $ boocons s in -- rewind for next use
      set_boocons ngs' s




data NoGoodStore = NoGoodStore { program_nogoods :: [Clause] -- program nogoods
                               , learned_nogoods :: [Clause] -- learned nogoods
                               , png_akku        :: [Clause] -- program nogoods akku
                               , lng_akku        :: [Clause] -- learned nogoods akku
                               , counter         :: Int
} deriving (Show, Eq)


new_ngs :: [Clause] -> [Clause] -> NoGoodStore
new_ngs png lng = NoGoodStore png lng [] [] (-1)


ngs_size :: NoGoodStore -> Int
ngs_size (NoGoodStore png lng _ _ _) = (length png) + (length lng)


p_nogoods ngs = (program_nogoods ngs) ++ (png_akku ngs)
l_nogoods ngs = (learned_nogoods ngs) ++ (lng_akku ngs)


get_ng :: NoGoodStore -> Clause
-- get current nogood
get_ng (NoGoodStore png lng _ _ counter) =
  if counter < length png
  then png!!counter
  else
    if counter < (length png) + (length lng)
    then lng!!(counter-length png)
    else error "NoGoodStore out of bounds"


add_nogoods :: [Clause] -> NoGoodStore -> NoGoodStore
add_nogoods ngs (NoGoodStore png lng pnga lnga c) =
  (NoGoodStore png (lng++ngs) pnga lnga c) 


rewind :: NoGoodStore -> NoGoodStore
-- basically reset the nogood store because some resolvent was found
rewind (NoGoodStore png lng pnga lnga counter) =
  if counter < length png
  then 
    let png' = png ++ pnga in
    (NoGoodStore png' lng [] [] (-1))
  else
    let png' = png ++ pnga
        lng' = lng ++ lnga 
    in
    NoGoodStore png' lng' [] [] (-1)



upgrade_ngs :: NoGoodStore -> Clause -> NoGoodStore
-- replace current nogood with new nogood reset nogood store
upgrade_ngs (NoGoodStore png lng pnga lnga counter) ng =
  if counter < length png
  then 
    let png'  = drop (counter+1) png
        pnga' = (take counter png) ++ (ng:pnga) 
    in
    (NoGoodStore png' lng pnga' lnga (-1))
  else
    let png'  = []
        pnga' = png++pnga
        lng'  = drop (counter+1-length png) lng
        lnga' = (take (counter-length png) lng)++(ng:lnga) 
    in
    NoGoodStore png' lng' pnga' lnga' (-1)


up_rew_ngs :: NoGoodStore -> Clause -> NoGoodStore
-- upgrade and rewind
up_rew_ngs (NoGoodStore png lng pnga lnga counter) ng =
  if counter < length png
  then 
    let png' = ng: ((take counter png) ++ (drop (counter+1) png) ++ pnga) in
    (NoGoodStore png' lng [] [] (-1))
  else
    let png' = png++pnga
        lng' = ng:((take (counter-length png) lng) ++ (drop (counter+1-length png) lng) ++ lnga)
    in
    (NoGoodStore png' lng' [] [] (-1))



get_svar :: SPVar -> [SPVar] -> SVar
get_svar l x = get_svar2 l x 0

get_svar2 :: SPVar -> [SPVar] -> Int -> SVar
get_svar2 s (f:ls) n =
  if s==f
  then n
  else get_svar2 s ls (n+1)


get_svarx :: [SPVar] -> SPVar -> SVar
get_svarx x l = get_svar2 l x 0


transforms :: [CClause] -> [SPVar] -> [Clause]

transforms [] _ = []

transforms (c:cs) spvars = ((transform c spvars):(transforms cs spvars))


transform :: CClause -> [SPVar] -> Clause
transform (t,f) spvars =
  let l              = length spvars
      a              = initialAssignment l
      tsvars         = map (get_svarx spvars) t
      fsvars         = map (get_svarx spvars) f
      a'             = assign_trues (assign_falses a fsvars) tsvars
      allvars        = tsvars++fsvars
      number_of_vars = length allvars
  in
  if number_of_vars == 1
  then (a', head allvars, head allvars)
  else 
    let w = head allvars
        v = head (tail allvars)
    in
    (a',w,v)

assign_trues :: Assignment -> [SVar] -> Assignment
assign_trues a [] = a
assign_trues a (v:vs) = assign_trues (assign a (T v) 1) vs

assign_falses :: Assignment -> [SVar] -> Assignment
assign_falses a [] = a
assign_falses a (v:vs) = assign_falses (assign a (F v) 1) vs


-- -----------------------------------------------------------------------------

-- Conflict Driven Nogood Learning - Enumeration

data TSolver = TSolver { 
                         program                  :: [Rule]      -- the program
                       , spvars                   :: [SPVar]     --
                       , boocons                  :: NoGoodStore -- the store of boolean constraints
                       , decision_level           :: Int         -- the decision level 
                       , blocked_level            :: Int         -- the blocked level
                       , assignment_level         :: Int         -- the assignment level
                       , assignment               :: Assignment  -- an assignment
                       , dliteral_tracker         :: [(Int,SignedVar)]
                       , assignment_level_tracker :: [(Int,Int)]      
                       , get_unfounded_set        :: [Atom]      -- unfounded atoms
                       , conf                     :: Bool        -- is the state of the solver in conflict
                       } deriving (Show, Eq)

set_program :: [Rule] -> TSolver -> TSolver
set_program p                    (TSolver _ spvars ngs dl bl al a dlt alt u c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_spvars spvars                (TSolver p _      ngs dl bl al a dlt alt u c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_boocons ngs                  (TSolver p spvars _   dl bl al a dlt alt u c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_decision_level dl            (TSolver p spvars ngs _  bl al a dlt alt u c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_blocked_level bl             (TSolver p spvars ngs dl _  al a dlt alt u c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_assignment_level al          (TSolver p spvars ngs dl bl _  a dlt alt u c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_assignment a                 (TSolver p spvars ngs dl bl al _ dlt alt u c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_dliteral_tracker dlt         (TSolver p spvars ngs dl bl al a _   alt u c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_assignment_level_tracker alt (TSolver p spvars ngs dl bl al a dlt _   u c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_unfounded_set u              (TSolver p spvars ngs dl bl al a dlt alt _ c) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
set_conf c                       (TSolver p spvars ngs dl bl al a dlt alt u _) = (TSolver p spvars ngs dl bl al a dlt alt u c) 
 

cdnl_enum :: [Rule] -> Int -> [[Atom]]

cdnl_enum prg s =
  let cngs   = nub (nogoods_of_lp prg)
      vars   = get_vars cngs
      png    = transforms cngs vars
      ngs    = new_ngs png []
      l      = length vars
      dl     = 1
      bl     = 1
      al     = 1
      a      = initialAssignment l
      dlt    = []
      alt    = [(1,1)]
      u      = []
      conf   = False
      solver = TSolver prg vars ngs dl bl al a dlt alt u conf
  in
  cdnl_enum_loop solver 0  




conflict_handling :: TSolver -> TSolver
-- should resolve the conflict learn a new maybe clause and backtrack the solver
conflict_handling s =
  let a        = assignment s
      bl       = blocked_level s
      dl       = decision_level s
      alt      = assignment_level_tracker s
      dliteral = dliteral_tracker s
  in
  if bl < dl
  then                                                                       -- learn a new nogood and backtrack
    let ccl          = get_ng $ boocons s
        png          = p_nogoods $ boocons s
        lng          = l_nogoods $ boocons s
        (learnednogood, sigma_uip, alx) = conflict_analysis alt (png++lng) ccl a
        ngs'         = add_nogoods [learnednogood] $ boocons s 
                                                                                                   -- backtrack
        bt_dl        = al2dl alt alx
        bt_al        = dl2al alt bt_dl
        a'           = assign (backtrack a bt_al) (invert sigma_uip) bt_al
        dliteral'    = dlbacktrack dliteral bt_dl
        alt'         = albacktrack alt bt_dl
   
        solver       = set_decision_level (bt_dl-1)        $
                       set_dliteral_tracker dliteral'    $
                       set_assignment_level_tracker alt' $
                       set_assignment_level (bt_al+1) $ set_assignment a' $ set_boocons ngs' s
    in
    solver
  else                                                                                              -- backtrack
    let sigma_d      = get_dliteral dliteral dl
        dl'          = dl-1
        bl'          = dl'
        bt_al        = dl2al alt dl'
        a'           = assign (backtrack a bt_al) (invert sigma_d) bt_al
        alt'         = albacktrack alt dl'

        solver       = set_decision_level dl'            $
                       set_blocked_level bl'             $
                       set_assignment_level_tracker alt' $
                       set_assignment_level bt_al $ set_assignment a' s
    in
    solver


cdnl_enum_loop ::
  TSolver                  -- the solver
  -> Int                   -- s
  -> [[Atom]]              -- answer sets
cdnl_enum_loop solver s =
  let
    solverp = set_unfounded_set [] $ set_conf False solver 
    solver' = nogood_propagation solverp
    dl      = decision_level solver'
  in
  if conf solver'
  then -- conflict
    if dl == 1
    then []                                                  -- no need for conflict handling, no more answer sets
    else                                                                                      -- conflict handling
      let solver'' = conflict_handling solver' in
      cdnl_enum_loop solver'' s

  else -- no conflict
    let 
      a'         = assignment solver'
      al'        = assignment_level solver'
      dlt        = dliteral_tracker solver'
      alt        = assignment_level_tracker solver'
      selectable = get_unassigned a' 
    in
    if null selectable
    then                                                                     -- if all atoms then answer set found
      let s2= s-1 in
      if dl==1 || s2==0
      then [nub (trueatoms a' (spvars solver'))]                                                -- last answer set
      else                                                                  -- backtrack for remaining answer sets
        let
            sigma_d      = get_dliteral dlt dl
            dlt'    = dlbacktrack dlt dl
            cal          = dl2al alt dl
            alt'         = albacktrack alt dl
            a''          = backtrack a' cal
            a'''         = assign a'' (invert sigma_d) cal                         -- invert last decision literal
            dl'          = dl-1
            bl'          = dl'
            solver''     = set_decision_level dl'            $
                           set_blocked_level bl'             $
                           set_dliteral_tracker dlt'          $
                           set_assignment_level_tracker alt' $
                           set_assignment_level (cal+1)      $ set_assignment a''' solver'
            remaining_as = cdnl_enum_loop solver'' s2 
        in
        (nub (trueatoms a' (spvars solver'))):remaining_as
    else                                                                                         -- select new lit
      let sigma_d      = head selectable
          dlt'         = ((dl+1),(T sigma_d)):dlt
          alt'         = (al',dl+1):alt
          a''          = assign a' (T sigma_d) al'
          solver''     = set_decision_level (dl+1)         $
                         set_dliteral_tracker dlt'         $
                         set_assignment_level_tracker alt' $
                         set_assignment_level (al'+1) $ set_assignment a'' solver'
          remaining_as = cdnl_enum_loop solver'' s
      in
      remaining_as


al2dl :: [(Int,Int)] -> Int -> Int
al2dl ((al1,dl1):rest) al =
  if al<al1
  then al2dl rest al
  else dl1

dl2al :: [(Int,Int)] -> Int -> Int
dl2al ((al1,dl1):rest) dl =
  if dl==dl1
  then al1
  else dl2al rest dl

albacktrack :: [(Int,Int)] -> Int -> [(Int,Int)]
albacktrack alt l = [ (al,dl) | (al,dl) <- alt, dl < l ]

type DLT = [(Int,SignedVar)]                                                    -- DecisionLevelTracker

get_dliteral :: DLT -> Int -> SignedVar

get_dliteral ((dl1,sl1):xs) l
  | dl1 == l = sl1
  | otherwise = get_dliteral xs l

dlbacktrack :: DLT -> Int -> DLT
-- backtracks the decision levels
dlbacktrack dlt l = [ (dl,sl) | (dl,sl) <- dlt, dl < l ]



conflict_analysis :: [(Int,Int)] -> [Clause] -> Clause -> Assignment -> (Clause, SignedVar, Int)
conflict_analysis alt nogoods nogood assig =
  let (sigma, prefix) = get_sigma nogood assig
      dl_sigma        = get_alevel assig sigma
      reduced_nogood  = clauseWithoutSL nogood sigma
      k               = get_max_alevel reduced_nogood assig
      dl              = al2dl alt dl_sigma
      al              = dl2al alt dl
      rhos            = filter_al nogood assig al in
  if only rhos sigma
  then (nogood, sigma, k)
  else
    let
      eps         = get_epsilon nogoods sigma prefix
      reduced_eps = clauseWithoutSL eps (invert sigma)
      newnogood   = joinClauses reduced_nogood reduced_eps
    in
    conflict_analysis alt nogoods newnogood prefix



get_epsilon :: [Clause] -> SignedVar -> Assignment -> Clause

get_epsilon [] l prefix =  error "no antecedent epsilon found"

get_epsilon (ng:ngs) sigma prefix =
  let temp = clauseWithoutSL ng (invert sigma) in
  if is_included temp prefix
  then ng
  else get_epsilon ngs sigma prefix



-- Propagation


tight :: [Rule] -> Bool  -- TODO implement tightness check
tight p = False


nogood_propagation :: TSolver -> TSolver
nogood_propagation s =
  let
    prg = program s 
    spv = spvars s
    u   = get_unfounded_set s 
    s'  = local_propagation s
    a   = assignment s'
    al  = assignment_level s'
    ngs = boocons s'
    png = p_nogoods ngs
    lng = l_nogoods ngs
  in
  if conf s'
  then  s'
  else
    if tight prg
    then s'
    else
      case ufs_check (prg, a, spv, u) of                  -- unfounded set check
        [] -> s' 
        u' -> let p = get_svar (ALit (head u')) spv in
              if elemAss (T p) a
              then
                let cngs_of_loop = loop_nogoods prg u'
                    ngs_of_loop  = transforms cngs_of_loop spv
                    ngs'         = add_nogoods ngs_of_loop ngs
                in
                set_boocons ngs' s'
              else
                if elemAss (F p) a
                then
                  let s'' =                                                   set_unfounded_set u' s' in
                  nogood_propagation s''
                else 
                  let a'  = assign a (F p) al                    -- extend assignment  
                      s'' = set_assignment_level (al+1) $ set_assignment a' $ set_unfounded_set u' s'
                  in
                  nogood_propagation s''



ufs_check ::
  ( [Rule]     -- program
  , Assignment 
  , [SPVar]
  , [Atom]     -- possibly unfounded set
  ) -> [Atom]
ufs_check (prg, a, spvars, u) =
  if null (u \\ (falseatoms a spvars))
  then                                                    
    unfounded_set prg a spvars 
  else u \\ (falseatoms a spvars)

