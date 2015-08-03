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
canchoose (NoGoodStore png lng pnga lnga counter) =
  if (counter+1) < (length png) + (length lng) 
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


cdnl_enum :: [Rule] -> Int -> [[Atom]]

cdnl_enum prg s =
  let cngs = nub (nogoods_of_lp prg)
      vars = get_vars cngs
      l    = length vars
      assi = initialAssignment l
      ngs  = transforms cngs vars
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

cdnl_enum_loop prg s dl bl al dliteral alt png lng a spvars =
  let
--    solver  = TSolver
--    solver' = ngprop2 solver
    (maybeassig,al',png',lng') = ng_prop prg al png lng a spvars []
  in
  case maybeassig of
    Conflict ccl cass -> -- conflict
                         if dl == 1
                         then []                                                                     -- no more answer sets
                         else                                                                        -- conflict analysis and backtrack
                           if bl < dl
                           then
                             let (learnednogood, sigma_uip, alx) = conflict_analysis alt (png'++lng') ccl cass
                                 dl'       = al2dl alt alx
                                 al''      = dl2al alt dl'
                                 lng''     = learnednogood:lng'
                                 a'        = assign (backtrack cass al'') (invert sigma_uip) al''
                                 dliteral' = dlbacktrack dliteral dl'
                                 alt'      = albacktrack alt dl'
                             in
                             cdnl_enum_loop prg s (dl'-1) bl (al''+1) dliteral' alt' png' lng'' a' spvars
                           else
                             let sigma_d      = get_dliteral dliteral dl
                                 dl'          = dl-1
                                 bl'          = dl'
                                 al''         = dl2al alt dl'
                                 a'           = assign (backtrack cass al'') (invert sigma_d) al''
                                 alt'         = albacktrack alt dl'
                                 remaining_as = cdnl_enum_loop prg s dl' bl' al'' dliteral alt' png' lng' a' spvars
                             in
                             remaining_as

    ASSIGNMENT a'     -> -- no conflict
                         let selectable = get_unassigned a' in
                         if null selectable
                         then                                                                       -- if all atoms then answer set found
                           let s2= s-1 in
                           if dl==1 || s2==0
                           then [nub (trueatoms a' spvars)]                                     -- last answer set
                           else                                                                     -- backtrack for remaining answer sets
                             let
                                 sigma_d      = get_dliteral dliteral dl
                                 dl'          = dl-1
                                 bl'          = dl'
                                 dliteral'    = dlbacktrack dliteral dl
                                 cal          = dl2al alt dl
                                 alt'         = albacktrack alt dl
                                 a''          = backtrack a' cal
                                 a'''         = assign a'' (invert sigma_d) cal                         -- invert last decision literal
                                 remaining_as = cdnl_enum_loop prg s2 dl' bl' (cal+1) dliteral' alt' png' lng' a''' spvars
                             in
                             (nub (trueatoms a' spvars)):remaining_as
                         else                                                                        -- select new lit
                           let sigma_d   = head selectable
                               dliteral' = (((dl+1),(T sigma_d)):dliteral)
                               alt'      = ((al',dl+1):alt)
                               a''       = assign a' (T sigma_d) (al')
                           in
                           cdnl_enum_loop prg s (dl+1) bl (al'+1) dliteral' alt' png' lng' a'' spvars


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



-- -----------------------------------------------------------------------------

data TSolver = TSolver { 
                         program          :: [Rule]      -- the program
                       , spvars           :: [SPVar]     --
                       , boocons          :: NoGoodStore -- the store of boolean constraints
                       , assignment       :: Assignment  -- an assignment
                       , assignment_level :: Int         -- the assignment level
                       , get_unfounded_set    :: [Atom]      -- unfounded atoms
                       , conf             :: Bool        -- is the state of the solver in conflict
                       } deriving (Show, Eq)

set_program :: [Rule] -> TSolver -> TSolver
set_program p           (TSolver _ spvars ngs a al u c) = (TSolver p spvars ngs a al u c)
set_assignment a        (TSolver p spvars ngs _ al u c) = (TSolver p spvars ngs a al u c)
set_assignment_level al (TSolver p spvars ngs a _ u c)  = (TSolver p spvars ngs a al u c)
set_boocons ngs         (TSolver p spvars _ a al u c)   = (TSolver p spvars ngs a al u c)
set_spvars spvars       (TSolver p _ ngs a al u c)      = (TSolver p spvars ngs a al u c)
set_unfounded_set u     (TSolver p spvars ngs a al _ c) = (TSolver p spvars ngs a al u c)
set_conf c              (TSolver p spvars ngs a al u _) = (TSolver p spvars ngs a al u c)


-- Propagation

data PropRes = ASSIGNMENT Assignment  -- result of propagation can either be a conflict or a new assignment
             | Conflict Clause Assignment
             deriving (Show,Eq)


tight :: [Rule] -> Bool  -- TODO implement tightness check
tight p = False


ng_prop2 :: TSolver -> TSolver
ng_prop2 s =
  let
    -- ngs    = new_ngs png lng 
    s'  = local_propagation s
    prg = program s'
    a   = assignment s'
    al  = assignment_level s'
    ngs = boocons s'
    png = p_nogoods ngs
    lng = l_nogoods ngs
    u   = get_unfounded_set s'
  in
  if conf s'
  then
    let conf_ng = get_ng ngs in
    s'
  else
    if tight prg
    then s'
    else
      case ufs_check (prg, a, (spvars s'), u) of                  -- unfounded set check
        [] -> s' 
        u' -> let p = get_svar (ALit (head u')) (spvars s') in
              if elemAss (T p) a
              then
                let cngs_of_loop = loop_nogoods prg u'
                    ngs_of_loop  = transforms cngs_of_loop (spvars s')
                    ngs' = add_nogoods ngs_of_loop ngs
                in
                set_boocons ngs' s'
              else
                if elemAss (F p) a
                then
                  let s'' =                     set_unfounded_set u' s' in
                  ng_prop2 s''
                else 
                  let a'  = assign a (F p) al                    -- extend assignment  
                      s'' = set_assignment a' $ set_unfounded_set u' s'
                  in
                  ng_prop2 s''



ng_prop :: 
  [Rule]           -- program
  -> Int           -- assignment level
  -> [Clause]      -- program nogoods
  -> [Clause]      -- learned no goods
  -> Assignment 
  -> [SPVar]      
  -> [Atom]        --
  -> (PropRes,Int,[Clause],[Clause])
ng_prop prg al png lng a spvars u =
  let
    ngs    = new_ngs png lng 
    s      = TSolver prg spvars ngs a al u False
    s'     = local_propagation s
    a'     = assignment s'
    al'    = assignment_level s'
    ngs'   = boocons s'
    png'   = p_nogoods ngs'
    lng'   = l_nogoods ngs'
  in
  if conf s'
  then
    let conf_ng = get_ng ngs' in
    (Conflict conf_ng a', al', png', lng')                    -- return conflic nogood
  else
    if tight prg
    then (ASSIGNMENT a', al', png', lng')
    else
      case ufs_check (prg, a', spvars, u) of                  -- unfounded set check
        [] -> (ASSIGNMENT a', al', png', lng') 
        u' -> let p = get_svar (ALit (head u')) spvars in
              if elemAss (T p) a'
              then
                let cngs_of_loop = loop_nogoods prg u'
                    ngs_of_loop  = transforms cngs_of_loop spvars
                in
                (ASSIGNMENT a', al', png', ngs_of_loop++lng')
              else
                let a'' = assign a' (F p) al in               -- extend assignment
                case elemAss (F p) a' of
                  True  -> ng_prop prg al' png' lng a'  spvars u'
                  False -> ng_prop prg al' png' lng a'' spvars u'



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

