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

data TSolver = TSolver { boocons          :: NoGoodStore -- list of clauses/boolean constraints
                       , assignment_level :: Int         -- assignmenetlevel
                       , assig            :: Assignment  -- an assignment
                       , conf             :: Bool        -- is the state of the solver cons or incons
                       } deriving (Show, Eq)


choose :: TSolver -> TSolver
choose s =
  if (conf s)
  then s
  else TSolver (choose2 $ boocons s) (assignment_level s) (assig s) (conf s)



canchoose :: NoGoodStore -> Bool
-- returns true if not all nogoods have been tested
canchoose (NoGoodStore png lng pnga lnga counter) =
  if (counter+1) <  (length png) + (length lng) 
  then True
  else False

choose2 :: NoGoodStore -> NoGoodStore
-- is only called if canchoose return true
choose2 (NoGoodStore png lng pnga lnga counter) = (NoGoodStore png lng pnga lnga (counter+1))


resolv :: TSolver -> TSolver
-- is only called if conf is false
resolv s =
    let al = (assignment_level s)
        ng = get_ng (boocons s)
        x  = resolve al ng (assig s)
    in
    case x of
       NIX         -> s
       NIXU ng'    -> let ngs' = upgrade_ngs (boocons s) ng' in
                      TSolver ngs' al (assig s) (conf s)
                                                                                                                      
       Res a'      -> let ngs' = rewind (boocons s) in
                      TSolver ngs' (al+1) a' (conf s)      
 
       ResU a' ng' -> let ngs' =  up_rew_ngs (boocons s) ng' in
                      TSolver ngs' (al+1) a' (conf s)
                                                                                                                      
       CONF        -> TSolver (boocons s) al (assig s) True     -- set conflict

      


local_propagation :: TSolver -> TSolver
local_propagation s =
  if conf s
  then s
  else 
    if canchoose (boocons s)
    then local_propagation $ resolv $ (choose s)
    else s


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

get_ng :: NoGoodStore -> Clause
-- get current nogood
get_ng (NoGoodStore png lng _ _ counter) =
  if counter < length png
  then png!!counter
  else
    if counter < (length png) + (length lng)
    then lng!!(counter-length png)
    else error "NoGoodStore out of bounds"

p_nogoods ngs = (program_nogoods ngs) ++ (png_akku ngs)
l_nogoods ngs = (learned_nogoods ngs) ++ (lng_akku ngs)





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
    (NoGoodStore png' lng' [] [] (-1))



upgrade_ngs :: NoGoodStore -> Clause -> NoGoodStore
-- replace current nogood with new nogood reset nogood store
upgrade_ngs (NoGoodStore png lng pnga lnga counter) ng =
  if counter < length png
  then 
    let png'  = drop (counter+1) png
        pnga' = (take counter png) ++ (ng:pnga) in
    (NoGoodStore png' lng pnga' lnga (-1))
  else
    let png'  = []
        pnga' = png++pnga
        lng'  = drop (counter+1-length png) lng
        lnga' = (take (counter-length png) lng)++(ng:lnga) in
    (NoGoodStore png' lng' pnga' lnga' (-1))


up_rew_ngs :: NoGoodStore -> Clause -> NoGoodStore
-- upgrade and rewind
up_rew_ngs (NoGoodStore png lng pnga lnga counter) ng =
  if counter < length png
  then 
    let png' = (ng: ((take counter png) ++ (drop (counter+1) png) ++ pnga)) in
    (NoGoodStore png' lng [] [] (-1))
  else
    let png'  = png++pnga
        lng'  = (ng: ((take (counter-length png) lng) ++ (drop (counter+1-length png) lng) ++ lnga)) in
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
  then (a',head allvars,head allvars)
  else 
    let w= head allvars
        v= head (tail allvars)
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


cdnl_enum :: [Rule] -> Int -> [[Atom]]

cdnl_enum prg s =
  let cngs = (nub (nogoods_of_lp prg))
      vars = get_vars cngs
      l    = length vars
      assi = initialAssignment l
      ngs  =  transforms cngs vars
  in
  cdnl_enum_loop prg 0 1 1 1 [] [(1,1)] ngs [] assi vars


cdnl_enum_loop ::
  [Rule]                   -- the program
  -> Int                   -- s
  -> Int                   -- decision level
  -> Int                   -- blocked level
  -> Int                   -- assignment level
  -> [(Int,SignedVar)]     -- decision level tracker
  -> [(Int,Int)]           -- al2dl
  -> [Clause]              -- program nogoods
  -> [Clause]              -- learned nogoods
  -> Assignment
  -> [SPVar]               -- maging SPVar 2 SVar(Int)
  -> [[Atom]]              -- found answer sets

cdnl_enum_loop prg s dl bl al dliteral alt ngs_p ngs assig spvars =
  let
    (maybeassig,al2,ngs_p',ngs') = ng_prop prg al ngs_p ngs assig spvars []
  in
  case maybeassig of
    Conflict ccl cass -> -- conflict
                         if dl==1
                         then []                                                                     -- no more answer sets
                         else                                                                        -- conflict analysis and backtrack
                           if bl < dl
                           then
                             let (learnednogood, sigma_uip, alx) = conflict_analysis alt (ngs_p'++ngs') ccl cass
                                 dl3       = (al2dl alt alx)
                                 al3       = dl2al alt dl3
                                 ngs''     = (learnednogood:ngs')
                                 assig3    = assign (backtrack cass al3) (invert sigma_uip) (al3)
                                 dliteral2 = dlbacktrack dliteral dl3
                                 alt2      = albacktrack alt dl3
                             in
                             cdnl_enum_loop prg s (dl3-1) bl (al3+1) dliteral2 alt2 ngs_p' ngs'' assig3 spvars
                           else
                             let sigma_d      = (get_dliteral dliteral (dl))
                                 dl2          = dl-1
                                 bl2          = dl2
                                 al3          = (dl2al alt dl2)
                                 assig3       = assign (backtrack cass al3) (invert sigma_d) al3
                                 alt2         = albacktrack alt dl2
                                 remaining_as = cdnl_enum_loop prg s dl2 bl2 al3 dliteral alt2 ngs_p' ngs' assig3 spvars
                             in
                             remaining_as

    ASSIGNMENT assig2 -> -- no conflict
                         let selectable = get_unassigned assig2 in
                         if null selectable
                         then                                                                       -- if all atoms then answer set found
                           let s2= s-1 in
                           if (dl==1 || s2==0)
                           then [nub (trueatoms assig2 spvars)]                                     -- last answer set
                           else                                                                     -- backtrack for remaining answer sets
                             let
                                 sigma_d      = (get_dliteral dliteral (dl))
                                 dl2          = dl-1
                                 bl2          = dl2
                                 dliteral2    = dlbacktrack dliteral dl
                                 cal          = (dl2al alt dl)
                                 alt2         = albacktrack alt dl
                                 assig3       = backtrack assig2 cal
                                 assig4       = assign assig3 (invert sigma_d) cal                         -- invert last decision literal
                                 remaining_as = cdnl_enum_loop prg s2 dl2 bl2 (cal+1) dliteral2 alt2 ngs_p' ngs' assig4 spvars
                             in
                             ((nub (trueatoms assig2 spvars)):remaining_as)
                         else                                                                        -- select new lit
                           let sigma_d = head selectable
                               dliteral2 = (((dl+1),(T sigma_d)):dliteral)
                               alt2 = ((al2,dl+1):alt)
                               assig3 = assign assig2 (T sigma_d) (al2)
                           in
                           cdnl_enum_loop prg s (dl+1) bl (al2+1) dliteral2 alt2 ngs_p' ngs' assig3 spvars


al2dl:: [(Int,Int)] -> Int -> Int
al2dl ((al1,dl1):rest) al =
  if al<al1
  then al2dl rest al
  else dl1

dl2al:: [(Int,Int)] -> Int -> Int
dl2al ((al1,dl1):rest) dl =
  if dl==dl1
  then al1
  else dl2al rest dl

albacktrack:: [(Int,Int)] -> Int -> [(Int,Int)]
albacktrack alt l = [ (al,dl) | (al,dl) <- alt, dl < l ]

type DLT = [(Int,SignedVar)]                                                    -- DecisionLevelTracker

get_dliteral:: DLT -> Int -> SignedVar

get_dliteral ((dl1,sl1):xs) l
  | dl1 == l = sl1
  | otherwise = get_dliteral xs l

dlbacktrack:: DLT -> Int -> DLT
-- backtracks the decision levels
dlbacktrack dlt l = [ (dl,sl) | (dl,sl) <- dlt, dl < l ]



conflict_analysis:: [(Int,Int)] -> [Clause] -> Clause -> Assignment -> (Clause, SignedVar, Int)
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
  else (get_epsilon ngs sigma prefix)



-- -----------------------------------------------------------------------------

-- Propagation

data PropRes =  ASSIGNMENT Assignment  -- result of propagation can either be a conflict or a new assignment
         | Conflict Clause Assignment
         deriving (Show,Eq)


tight :: [Rule] -> Bool  -- TODO implement tigness check
tight p = False

ng_prop :: [Rule] -> Int -> [Clause] -> [Clause] -> Assignment -> [SPVar] -> [Atom] -> (PropRes,Int,[Clause],[Clause])
ng_prop prg al png lng a spvars u =
  let
    spc    = initspc prg
    ngs    = new_ngs png lng 
    s      = TSolver ngs al a False
    s'     = local_propagation s
    a'     = assig s'
    al'    = assignment_level s'
    ngs'   = boocons s'
    png'   = p_nogoods ngs'
    lng'   = l_nogoods ngs'
  in
  if conf s'
  then
    let conflict_nogood  = get_ng ngs' in
    (Conflict conflict_nogood a', al', png', lng')            -- return conflic nogood
  else
    if tight prg
    then (ASSIGNMENT a', al', png', lng')
    else 
      let u2 = u \\ (falseatoms a' spvars) in      -- non false atoms
      if null u2
      then                                                    -- unfounded set check
        let u3 = (unfounded_set prg spc a' spvars) in
        if null u3
        then (ASSIGNMENT a', al', png', lng')
        else                                                  -- learn loop nogood
          let p = get_svar ((ALit (head u3))) spvars in
          if elemAss (T p) a'
          then
            let cngs_of_loop = (loop_nogoods prg u3)
                ngs_of_loop = transforms cngs_of_loop spvars
            in
            (ASSIGNMENT a', al', png', (ngs_of_loop++lng'))
          else
            let a'' = assign a' (F p) al' in                  -- extend assignment
            case elemAss (F p) a' of
              True  -> ng_prop prg al' png' lng' a' spvars u3
              False -> ng_prop prg al' png' lng' a'' spvars u3
      else                                                    -- learn loop nogood from u2
        let p = get_svar ((ALit (head u2))) spvars
            cngs_of_loop = (loop_nogoods prg u2)
            ngs_of_loop = (transforms cngs_of_loop spvars)
        in
        if elemAss (T p) a'
        then (ASSIGNMENT a', al', png', (ngs_of_loop++lng'))
        else
          let a'' = assign a' (F p) al' in                    -- extend assignment
          if (elemAss (F p) a')
          then ng_prop prg al' png' (ngs_of_loop++lng') a' spvars u2
          else ng_prop prg al' png' (ngs_of_loop++lng') a'' spvars u2
   

