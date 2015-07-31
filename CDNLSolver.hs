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
import Grounder
import LPParser -- for parsing tests

data TSolver = TSolver { boocons:: NoGoodStore   -- list of clauses/boolean constraints
                       , assignment_level     :: Int        -- assignmenetlevel
                       , assig  :: Assignment -- an assignment
                       , conf   :: Bool       -- is the state of the solver cons or incons
                       } deriving (Show, Eq)

mpr1 = "a :- not b, not c.\n"
    ++ "b :- not a, not c.\n"
    ++ "c :- not a, not b.\n"
-- mpr1 = "a :- not b.\n"

Right mp1 = readProgram mpr1


tsolv = let cngs = (nub (nogoods_of_lp (groundProgram mp1)))
            vars = get_vars cngs
            l    = length vars
            assi = initialAssignment l
            ngs  = new_ngs (transforms cngs vars) [] 
        in 
        TSolver ngs 0 assi False


choose:: TSolver -> TSolver
choose s =
  if (conf s)
  then s
  else TSolver (choose2 $ boocons s) (assignment_level s) (assig s) (conf s)


--       if ((counter $ boocons s)+1) < ngs_size (boocons s)
--       then 
--         let (NoGoodStore png ln pnga lnga counter) = boocons s
--             ngs' = (NoGoodStore png ln pnga lnga (counter+1))
--         in 
--         TSolver ngs' (assignment_level s) (assig s) (conf s)
--       else s



canchoose :: NoGoodStore -> Bool
-- returns true if not all nogoods have been tested
canchoose (NoGoodStore png lng pnga lnga counter) =
  if (counter+1) <  (length png) + (length lng) 
  then True
  else False

choose2 :: NoGoodStore -> NoGoodStore
choose2 (NoGoodStore png lng pnga lnga counter) =
--  trace ("choose2: ") $ 
--  if (counter+1) <  (length png) + (length lng) 
--  then 
    (NoGoodStore png lng pnga lnga (counter+1))
--  else (NoGoodStore png lng pnga lnga counter)


resolv:: TSolver -> TSolver
resolv s =
  if (conf s)
  then s
  else  
    let al = (assignment_level s)
        ng = get_ng (boocons s)
        x  = resolve al ng (assig s)
    in
 --   trace ("resolv: " ++ (show (assig s)) ++ (show ng)) $
    case x of
       NIX         -> s
       NIXU ng'    -> let ngs' = upgrade_ngs (boocons s) ng' in
                      TSolver ngs' al (assig s) (conf s)
                                                                                                                      
       Res a'      -> let ngs' = rewind (boocons s) in
                      TSolver ngs' (al+1) a' (conf s)      
 
       ResU a' ng' -> let ngs' =  up_rew_ngs (boocons s) ng' in
                      TSolver ngs' (al+1) a' (conf s)
                                                                                                                      
       CONF ->        TSolver (boocons s) al (assig s) True     -- set conflict

      


prop:: TSolver -> TSolver
prop s =
--  trace ("prop: " ++ (show s)) $
  if (conf s)
  then s
  else 
    if canchoose (boocons s)
    then prop $ resolv $ (choose s)
    else s


data NoGoodStore = NoGoodStore { program_nogoods:: [Clause] -- program nogoods
                               , learned_nogoods:: [Clause] -- learned nogoods
                               , png_akku:: [Clause]        -- learned nogoods
                               , lng_akku:: [Clause]        -- learned nogoods
                               , counter:: Int
} deriving (Show, Eq)

new_ngs:: [Clause] -> [Clause] -> NoGoodStore
new_ngs png lng = NoGoodStore png lng [] [] (-1)

ngs_size:: NoGoodStore -> Int
ngs_size (NoGoodStore png lng _ _ _) = (length png) + (length lng)

get_ng:: NoGoodStore -> Clause
-- get current nogood
get_ng (NoGoodStore png lng _ _ counter) =
--  trace ("get_ng: " ++ (show counter)) $
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
--  trace ("rewind: ") $ 
  if counter < length png
  then 
    let png' = png ++ pnga in
    (NoGoodStore png' lng [] [] (-1))
  else
    let png' = png ++ pnga
        lng' = lng ++ lnga 
    in
    (NoGoodStore png' lng' [] [] (-1))



upgrade_ngs:: NoGoodStore -> Clause -> NoGoodStore
-- replace current nogood with new nogood reset nogood store
upgrade_ngs (NoGoodStore png lng pnga lnga counter) ng =
--  trace ("upgrade_ngs: ") $ 
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


up_rew_ngs:: NoGoodStore -> Clause -> NoGoodStore
-- upgrade and rewind
up_rew_ngs (NoGoodStore png lng pnga lnga counter) ng =
--  trace ("up_rew_ngs: ") $ 
  if counter < length png
  then 
    let png' = (ng: ((take counter png) ++ (drop (counter+1) png) ++ pnga)) in
    (NoGoodStore png' lng [] [] (-1))
  else
    let png'  = png++pnga
        lng'  = (ng: ((take (counter-length png) lng) ++ (drop (counter+1-length png) lng) ++ lnga)) in
    (NoGoodStore png' lng' [] [] (-1))



get_svar:: SPVar -> [SPVar] -> SVar
get_svar l x = get_svar2 l x 0

get_svar2:: SPVar -> [SPVar] -> Int -> SVar
get_svar2 s (f:ls) n =
  if s==f
  then n
  else get_svar2 s ls (n+1)


get_svarx:: [SPVar] -> SPVar -> SVar
get_svarx x l = get_svar2 l x 0


transforms:: [CClause] -> [SPVar] -> [Clause]

transforms [] _ = []

transforms (c:cs) spvars = ((transform c spvars):(transforms cs spvars))


transform:: CClause -> [SPVar] -> Clause
transform (t,f) spvars =
  let l = length spvars
      a = initialAssignment l
      tsvars = map (get_svarx spvars) t
      fsvars = map (get_svarx spvars) f
      a' = assign_trues (assign_falses a fsvars) tsvars
      allvars=tsvars++fsvars
      number_of_vars = length allvars
  in
  if number_of_vars == 1
  then (a',head allvars,head allvars)
  else let w= head allvars
           v= head (tail allvars)
       in
       (a',w,v)

assign_trues:: Assignment -> [SVar] -> Assignment
assign_trues a [] = a
assign_trues a (v:vs) = assign_trues (assign a (T v) 1) vs

assign_falses:: Assignment -> [SVar] -> Assignment
assign_falses a [] = a
assign_falses a (v:vs) = assign_falses (assign a (F v) 1) vs


-- -----------------------------------------------------------------------------

-- Conflict Driven Nogood Learning - Enumeration


cdnl_enum:: [Rule] -> Int -> [[Atom]]

cdnl_enum prg s =
  let cngs = (nub (nogoods_of_lp prg))
      vars = get_vars cngs
      l = length vars
      assi = initialAssignment l
      ngs =  transforms cngs vars
  in
  cdnl_enum_loop prg 0 1 1 1 [] [(1,1)] ngs [] assi vars


cdnl_enum_loop::
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
--   trace( "\ncdnl_loop:\n"
--   ++ (show spvars) ++ "\n"
--   ++ "assig:" ++ (show assig) ++ "\n"
--   ++ "dlits: " ++ (show dliteral)++ "\n"
--   ++ "al2dl: " ++ (show alt)) $
  case maybeassig of
    Conflict ccl cass -> -- conflict
 --                        trace( "Conf: " ++(show cass) ++ "\n") $
                         if dl==1
                         then []                                                                     -- no more answer sets
                         else                                                                        -- conflict analysis and backtrack
                           if bl < dl
                           then
                             let (learnednogood, sigma_uip, alx) = conflict_analysis alt (ngs_p'++ngs') ccl cass
                             in
--                              mtrace ("uip:  " ++ (show sigma_uip) ) $
--                              mtrace ("found al: " ++ (show alx) ++ " learnednogood: " ++ (show learnednogood) ) $
                             let
                                 dl3 = (al2dl alt alx)
                                 al3 = dl2al alt dl3
                             in
--                              mtrace ( "new al: " ++ (show al3) )$
                             let
                                 ngs'' = (learnednogood:ngs')
--                                  assigxxxx=(backtrack cass al3)
                                 assig3 = assign (backtrack cass al3) (invert sigma_uip) (al3)
                             in
--                              mtrace ( "btassig: " ++ (show assigxxxx) )$
--                              mtrace ( "neassig: " ++ (show assig3) ) $
                             let
                                 dliteral2 = dlbacktrack dliteral dl3
                                 alt2 = albacktrack alt dl3
                             in
--                              mtrace ("nedlits: " ++ (show dliteral2) ) $
--                              mtrace ("nealt  : " ++ (show alt2) ) $
                             cdnl_enum_loop prg s (dl3-1) bl (al3+1) dliteral2 alt2 ngs_p' ngs'' assig3 spvars
                           else
                             let sigma_d = (get_dliteral dliteral (dl))
                                 dl2 = dl-1
                                 bl2 = dl2
                                 al3 = (dl2al alt dl2)
                                 assig3 = assign (backtrack cass al3) (invert sigma_d) al3
                                 alt2 = albacktrack alt dl2
                                 remaining_as = cdnl_enum_loop prg s dl2 bl2 al3 dliteral alt2 ngs_p' ngs' assig3 spvars
                             in
                             remaining_as
    ASSIGNMENT assig2 -> -- no conflict
                         let
                             selectable = get_unassigned assig2
                         in
--                          mtrace( "Prop: " ++(show assig2) ++ "\n") $
                         if null selectable
                         then                                                                       -- if all atoms then answer set found
                           let s2= s-1 in
                           if (dl==1 || s2==0)
                           then                                                                     -- last answer set
  --                           trace ("AS: " ++ (show [nub (trueatoms assig2 spvars)])) $
                             [nub (trueatoms assig2 spvars)]
                           else                                                                     -- backtrack for remaining answer sets
                             let
                                 sigma_d = (get_dliteral dliteral (dl))
                                 dl2 = dl-1
                                 bl2 = dl2
                             in
--                              trace ("bt to: " ++ (show dl2)) $
                             let
                                 dliteral2 = dlbacktrack dliteral dl
                             in
--                              trace ("new dlits: " ++ (show dliteral2)) $
                             let
                                 cal = (dl2al alt dl)
                                 alt2 = albacktrack alt dl
                                 assig3 = backtrack assig2 cal
                                 assig4 = assign assig3 (invert sigma_d) cal                         -- invert last decision literal
                             in
--                              trace ("new al2dl: " ++ (show alt2)) $
--                              trace ("bt assig to:" ++ (show cal)) $
--                              trace ("assig3: " ++ (show assig3)) $
--                              trace ("assig4: " ++ (show assig4)) $
                             let
                                 remaining_as = cdnl_enum_loop prg s2 dl2 bl2 (cal+1) dliteral2 alt2 ngs_p' ngs' assig4 spvars
                             in
                           --  trace ("AS1: " ++ (show [nub (trueatoms assig2 spvars)])) $
                             ((nub (trueatoms assig2 spvars)):remaining_as)
                         else                                                                        -- select new lit
                           let sigma_d = head selectable
                               dliteral2 = (((dl+1),(T sigma_d)):dliteral)
                               alt2 = ((al2,dl+1):alt)
                               assig3 = assign assig2 (T sigma_d) (al2)
                           in
--                            mtrace ("al: " ++ (show al2)) $
--                           trace ( "choose: " ++ (show (T sigma_d))) $
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
      dl_sigma = get_alevel assig sigma
      reduced_nogood = clauseWithoutSL nogood sigma
      k = get_max_alevel reduced_nogood assig
      dl = al2dl alt dl_sigma
      al = dl2al alt dl
  in
--   mtrace ( "conflict_analysis: " ++ (show nogood) ++ (show assig) ++ (show sigma) ++ (show prefix) ) $
--   mtrace ( "ca: reduced_nogood: "++ (show reduced_nogood)) $
--   mtrace ( " dl_sigma: " ++ (show dl_sigma)) $
--   mtrace ( " alnew: " ++ (show al)) $
--   mtrace ( " k: " ++ (show k)) $
  let rhos = filter_al nogood assig al in
--   mtrace ( "rhos: " ++ (show rhos) ++ " sigma: " ++ (show sigma)) $
  if only rhos sigma
  then (nogood, sigma, k)
  else
    let
      eps = get_epsilon nogoods sigma prefix
      reduced_eps = clauseWithoutSL eps (invert sigma)
      newnogood = joinClauses reduced_nogood reduced_eps
    in
--     trace ( ">>> ca: reeps: "++ (show reduced_eps) ++ "redel: "++ (show reduced_nogood)  ++ "newnogood: "++ (show newnogood)) $
    conflict_analysis alt nogoods newnogood prefix



get_epsilon:: [Clause] -> SignedVar -> Assignment -> Clause

get_epsilon [] l prefix =  error "no antecedent epsilon found"

get_epsilon (ng:ngs) sigma prefix =
  let temp = clauseWithoutSL ng (invert sigma) in
--   mtrace ( "geteps: " ++ (show (sigma)) ++ (show ng) ++ (show temp) ++ (show prefix)
--   ++ " isincl: " ++ (show (is_included temp prefix))) $
  if is_included temp prefix
  then ng
  else (get_epsilon ngs sigma prefix)



-- -----------------------------------------------------------------------------

-- Propagation

data PropRes =  ASSIGNMENT Assignment  -- result of propagation can either be a conflict or a new assignment
         | Conflict Clause Assignment
         deriving (Show,Eq)


ng_prop::  [Rule] -> Int -> [Clause] -> [Clause] -> Assignment -> [SPVar] -> [Atom] -> (PropRes,Int,[Clause],[Clause])
ng_prop prg al ngs_p ngs assig spvars u =
  let
    spc = initspc prg
    (maybeassig,al2,ngs_p',ngs') = (local_propagation al (ngs_p,ngs) assig)
  in
  case maybeassig of                                                            -- TODO if prg is tight skip unfounded set check
    ASSIGNMENT assig2 ->
--        mtrace ( "unfound set check: "
--          ++ (show u)
--        ) $
       let u2 = u \\ (falseatoms assig2 spvars) in   -- non false atoms
--        mtrace ("unfounded set check") $
                            if null u2
                            then                                                -- unfounded set check
                              let u3 = (unfounded_set prg spc assig2 spvars) in
                              if null u3
                              then (ASSIGNMENT assig2,al2,ngs_p',ngs')
                              else                                              -- learn loop nogood
                                let
                                    p = get_svar ((ALit (head u3))) spvars
                                in
--                                 mtrace ("ufs found: "++(show u3)) $
                                if elemAss (T p) assig2
                                then
                                  let cngs_of_loop = (loop_nogoods prg u3)
                                      ngs_of_loop = transforms cngs_of_loop spvars
                                  in

                                  (ASSIGNMENT assig2,al2,ngs_p',(ngs_of_loop++ngs'))
                                else
                                  let
                                    assig3 = assign assig2 (F p) al2             -- extend assignment
                                  in
                                  case elemAss (F p) assig2 of
                                    True  -> ng_prop prg al2 ngs_p' ngs' assig2 spvars u3
                                    False -> ng_prop prg al2 ngs_p' ngs' assig3 spvars u3
                            else                                                -- learn loop nogood from u2
                              let
                                  p = get_svar ((ALit (head u2))) spvars
                                  cngs_of_loop = (loop_nogoods prg u2)
                                  ngs_of_loop = (transforms cngs_of_loop spvars)
                              in
                              if elemAss (T p) assig2
                              then (ASSIGNMENT assig2, al2,ngs_p',(ngs_of_loop++ngs'))
                              else
                                let
                                  assig3 = assign assig2 (F p) al2              -- extend assignment
                                in
                                if (elemAss (F p) assig2)
                                then
                                  ng_prop prg al2 ngs_p' (ngs_of_loop++ngs') assig2 spvars u2
                                else
                                  ng_prop prg al2 ngs_p' (ngs_of_loop++ngs') assig3 spvars u2

    Conflict ccl cass -> (Conflict ccl cass,al2,ngs_p',ngs')              -- return conflic clause



local_propagation::  Int -> ([Clause],[Clause]) -> Assignment -> (PropRes,Int,[Clause],[Clause])
-- takes a program a list of nogoods and an assignment and returns a propagation result

local_propagation al (pngs,lngs) a =
--  trace (">> loc_prop: " ++ (show a)) $ 
  -- no update of nogoods
  let assi   = a
      ngs    = new_ngs pngs lngs 
      s      = TSolver ngs al assi False
  in
--  trace (">>       s : " ++ (show s)) $
  let
      s'     = prop s
  in
--  trace ("loc_prop s': " ++ (show s')) $
  if conf s'
  then -- conflict with clause (counter s')
    let ngs' = boocons s' in
    (Conflict (get_ng ngs') (assig s'), (assignment_level s'), (p_nogoods $ boocons s'), (l_nogoods $ boocons s'))-- TODO update nogoods
  else -- no conflict
    (ASSIGNMENT (assig s'), (assignment_level s'), (p_nogoods $ boocons s'), (l_nogoods $ boocons s')) -- TODO update nogoods



-- local_propagation al ([],[],ngs_p,ngs) done todo a = local_propagation al (reverse ngs_p,reverse ngs,[],[]) done todo a
-- local_propagation al ([],ng:nogoods,r1,r2) done todo a =
--   let up = resolve al ng a  in
-- --   trace ("al: " ++ (show al)) $
--   case up of
--     NIX         -> if (done+1) == todo
--                    then (ASSIGNMENT a,al,r1,(ng:nogoods)++r2)
--                    else (local_propagation al ([],nogoods,r1,(ng:r2)) (done+1) todo a)
--     NIXU ng'    -> if (done+1) == todo
--                    then (ASSIGNMENT a,al,r1,(ng':nogoods)++r2)
--                    else (local_propagation al ([],nogoods,r1,(ng':r2)) (done+1) todo a)
-- 
--     Res a'      -> local_propagation (al+1) ([],nogoods,r1,(ng:r2)) 0 todo a'         -- increase assignment level
--     ResU a' ng' -> local_propagation (al+1) ([],nogoods,r1,(ng':r2)) 0 todo a'        -- increase assignment level
-- 
--     CONF -> (Conflict ng a,al,r1,(ng:nogoods)++r2)                                       -- return conflict clause
-- 
--     
-- local_propagation al (ng:nogoods,ngs,r1,r2) done todo a =
--   let up = resolve al ng a  in
-- --   trace ("al: " ++ (show al)) $
--   case up of
--     NIX         -> if (done+1) == todo
--                    then (ASSIGNMENT a,al,(ng:nogoods)++r1,ngs)
--                    else (local_propagation al (nogoods,ngs,(ng:r1),r2) (done+1) todo a)
--     NIXU ng'    -> if (done+1) == todo
--                    then (ASSIGNMENT a,al,(ng':nogoods)++r1,ngs)
--                    else (local_propagation al (nogoods,ngs,(ng':r1),r2) (done+1) todo a)
--                      
--     Res a'      -> local_propagation (al+1) (nogoods,ngs,(ng:r1),r2) 0 todo a'        -- increase assignment level
--     ResU a' ng' -> local_propagation (al+1) (nogoods,ngs,(ng':r1),r2) 0 todo a'       -- increase assignment level
--     
--     CONF -> (Conflict ng a,al,(ng:nogoods)++r1,ngs)                                       -- return conflict clause


-- data Res = ASSI Assignment  -- result of propagation can either be a conflict or a new assignment
--          | Conf Clause
--          | Nix
--          deriving (Show,Eq)
-- 
-- unitresult:: Int -> Assignment -> Clause -> Res
-- unitresult dl assig nogood =
--   case (resolve nogood assig) of
--     CONF  ->     {-mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig) ++ " = conflict") $-}
--                  Conf nogood
--     Res (T l) -> if isassigned l assig
--                  then
-- --                    mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig)) $
--                    Nix
--                  else
-- --                    mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig) ++ " = " ++ (show (T l))) $
--                    ASSI (assign assig (T l) dl)
--     Res (F l) -> if isassigned l assig
--                  then
-- --                    mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig)) $
--                    Nix
--                  else
-- --                    mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig) ++ " = " ++ (show (F l))) $
--                    ASSI (assign assig (F l) dl)
--     NIX       -> {-mtrace ("unitres: " ++ (show nogood) ++" "++ (show assig)) $-}
--                  Nix                                                            -- nothing can be derived
