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

module NGS (
   NogoodStore,
   Store,
   new_ngs,
   add_nogoods,
   get_nogoods,
   can_choose,
   choose,
   get_ng,
   up_rew,
   upgrade,
   rewind,
   Clause,
   fromCClause,
   conflict_resolution,
   RES(..),
   resolve,
) where

import Prelude (($), (+), (-), (*), abs, error)
import Data.Bool
import Data.Int
import Data.Maybe
import Data.Eq
import Data.Ord
import Text.Show
import SPVar
import Assignment as Ass
import DLT
import Data.Vector as BVec 
import Data.Vector.Unboxed as UVec
import Data.List as List
import Debug.Trace

-- little helper
get_svarx :: SymbolTable -> SPVar -> SVar
get_svarx st l = get_svar2 l st 0

get_svar2 :: SPVar -> SymbolTable -> Int -> SVar
get_svar2 s st i =
  if st BVec.!i == s
  then i
  else get_svar2 s st (i+1)



data Store a = Store { program_nogoods :: BVec.Vector a -- program nogoods
                     , learned_nogoods :: BVec.Vector a -- learned nogoods
                     , png_akku        :: BVec.Vector a -- program nogoods akku
                     , lng_akku        :: BVec.Vector a -- learned nogoods akku
                     , counter         :: Int
} deriving (Show, Eq)


new_ngs :: [a] -> [a] -> Store a
-- create a new store
new_ngs png lng = Store (BVec.fromList png) (BVec.fromList lng) (BVec.fromList []) (BVec.fromList []) (-1)


ngs_size :: Store a -> Int
-- return the size of the store
ngs_size (Store png lng _ _ _) = (BVec.length png) + (BVec.length lng)


get_nogoods ngs = (program_nogoods ngs) BVec.++ (png_akku ngs) BVec.++ (learned_nogoods ngs) BVec.++ (lng_akku ngs)


get_ng :: Store a -> a
-- get current nogood
get_ng (Store png lng _ _ counter) =
  let len_png = BVec.length png in
  if counter < len_png
  then png BVec.!counter
  else
    if counter < (len_png) + (BVec.length lng)
    then lng BVec.! (counter-len_png)
    else error "Store a out of bounds"


add_nogoods :: [a] -> Store a -> Store a
add_nogoods ngs (Store png lng pnga lnga c) =
  (Store png (lng BVec.++ (BVec.fromList ngs)) pnga lnga c) 


rewind :: Store a -> Store a
-- basically reset the nogood store because some resolvent was found
rewind (Store png lng pnga lnga counter) =
  if counter < BVec.length png
  then 
    let png' = png BVec.++ pnga in
    (Store png' lng (BVec.fromList []) (BVec.fromList []) (-1))
  else
    let png' = png BVec.++ pnga
        lng' = lng BVec.++ lnga
    in
    Store png' lng' (BVec.fromList []) (BVec.fromList []) (-1)


upgrade :: Store a -> a -> Store a
-- replace current nogood with new nogood reset nogood store
upgrade (Store png lng pnga lnga counter) ng =
  let len_png = BVec.length png in
  if counter < len_png
  then 
    let png'  = BVec.drop (counter+1) png
        pnga' = (BVec.take counter png) BVec.++ (BVec.cons ng pnga) 
    in
    (Store png' lng pnga' lnga (-1))
  else
    let png'  = BVec.fromList []
        pnga' = png BVec.++  pnga
        lng'  = BVec.drop (counter+1-len_png) lng
        lnga' = (BVec.take (counter-len_png) lng) BVec.++(BVec.cons ng lnga) 
    in
    Store png' lng' pnga' lnga' (-1)


up_rew :: Store a -> a -> Store a
-- upgrade and rewind
up_rew (Store png lng pnga lnga counter) ng =
  let len_png = BVec.length png in
  if counter < len_png
  then 
    let png' = BVec.snoc ((BVec.take counter png) BVec.++ (BVec.drop (counter+1) png) BVec.++ pnga) ng in
    (Store png' lng (BVec.fromList []) (BVec.fromList []) (-1))
  else
    let png' = png BVec.++ pnga
        lng' = BVec.snoc ((BVec.take (counter-len_png) lng) BVec.++ (BVec.drop (counter+1-len_png) lng) BVec.++ lnga) ng
    in
    (Store png' lng' (BVec.fromList []) (BVec.fromList []) (-1))


can_choose :: Store a -> Bool
-- returns true if not all nogoods have been tested
can_choose (Store png lng pnga lnga counter) = (counter+1) < (BVec.length png) + (BVec.length lng) 

choose :: Store a -> Store a
-- is only called if canchoose return true
choose (Store png lng pnga lnga counter) = (Store png lng pnga lnga (counter+1))


type NogoodStore = Store Clause


data RES = Res Assignment
         | ResU Assignment Clause
         | NIX
         | NIXU Clause         
         | CONF
         deriving Show


class (Eq s) => Nogood s where
  resolve :: Int -> s -> Assignment -> RES
  conflict_resolution :: NogoodStore -> s -> Assignment -> DLT -> (NogoodStore,SignedVar,Int)
  reduceNogood :: s -> SignedVar -> s
  is_satisfied :: s -> Assignment -> Bool


data Clause = UClause Int
            | BClause Int Int
            | Clause (UVec.Vector Int) {-# UNPACK #-} !Int {-# UNPACK #-} !Int
              deriving (Show,Eq) 


instance Nogood Clause where

  resolve al (UClause c) a =
      if c > 0 
      then
        if (a UVec.!(c-1) > 0)
        then CONF
        else
          if a UVec.!(c-1)==0
          then Res (assign a (F (c-1)) al)
          else NIX
      else
        if (a UVec.!((abs c)-1) < 0)
        then CONF
        else
          if a UVec.!((abs c)-1)==0
          then Res (assign a (T ((abs c)-1)) al)
          else NIX
 

  resolve al (BClause x y) a =
    let x' = a UVec.! ((abs x)-1)
        y' = a UVec.! ((abs y)-1)
    in
    if (x>0)
    then
      if x'<0
      then NIX
      else
        if x'>0
        then                                  --x>0             
          if y>0
          then
            if y'<0
            then NIX
            else         
              if y'>0
              then CONF                       -- x'>0, y>0
              else Res (assign a (F (y-1)) al)   -- x'>0, y'==0
          else                                -- x'>0, y < 0
            if y'>0
            then NIX
            else 
              if y'<0
              then CONF                       --x'>0, y'<0  
              else Res (assign a (T ((abs y)-1)) al)    --x'>0, y'==0
        else                                 --x'==0        
          if y>0
          then
            if y'<0
            then NIX
            else
              if y'>0
              then Res (assign a (F (x-1)) al)  --x'==0, y'>0
              else NIX                      --x'==0, y'==0
          else                             -- y < 0          
            if y'>0
            then NIX
            else 
              if y'<0
              then Res (assign a (F (x-1)) al)  -- x'==0, y'<0
              else NIX                      -- x'==0, y'==0

    else                                    -- x<0
      if x'>0
      then NIX
      else                                  
        if x'<0
        then                                --x'<0             
          if y>0
          then                              --y > 0
            if y'<0                         
            then NIX                       
            else         
              if y'>0                      
              then CONF                     --x'<0, y'>0
              else Res (assign a (F (y-1)) al)  --x'<0, y'==0
          else                              -- y < 0
            if y'>0
            then NIX
            else 
              if y'<0
              then CONF                     --x'<0, y'<0  
              else Res (assign a (T ((abs y)-1)) al)  --x'<0, y'==0
        else                               -- x'==0        
          if y>0
          then
            if y'<0
            then NIX
            else
              if y'>0
              then Res (assign a (T ((abs x)-1)) al)  -- x'==0, y'>0
              else NIX                      -- x'==0, y'==0
          else                              -- y<0
            if y'>0
            then NIX
            else 
              if y'<0
              then Res (assign a (T ((abs x)-1)) al)  -- x'==0, y'<0
              else NIX                      --x'==0, y'==0

 
  resolve al (Clause c v w) a =
    let v' = c UVec.!v in
    if v' > 0
    then
      if (a UVec.!(v'-1) < 0)            -- assigned
      then NIX
      else
        let w' = c UVec.!w in
        if (a UVec.!((abs w')-1) > 0 && w' < 0) || (a UVec.!((abs w')-1) < 0 && w' > 0)           -- assigned
        then NIX
        else 
          if a UVec.!(v'-1)==0
          then 
            if a UVec.!((abs w')-1)==0
            then NIX
            else updatewatch2 al (Clause c v w) a
          else updatewatch1 al (Clause c v w) a
    else
      if (a UVec.!((abs v')-1) > 0)             -- assigned
      then NIX
      else
        let w' = c UVec.!w in
        if (a UVec.!((abs w')-1) > 0 && w' < 0) || (a UVec.!((abs w')-1) < 0 && w' > 0)           -- assigned
        then NIX
        else 
          if a UVec.!((abs v')-1)==0
          then 
            if a UVec.!((abs w')-1)==0
            then NIX
            else updatewatch2 al (Clause c v w) a
          else updatewatch1 al (Clause c v w) a
  

  reduceNogood c l = reduceClause c l 

--  conflict_resolution :: NogoodStore -> Clause -> Assignment -> DLT -> (NogoodStore, SignedVar,Int)
  conflict_resolution ngs nogood a alt =
  --  trace ("conflict_res1: " List.++ (show nogood) List.++ (show a)) $
  --  trace ("DLT: " List.++ (show alt)) $
    let (ngs', sigma) = conflict_resolution2 ngs nogood a alt
        reduced_nogood  = reduceNogood nogood sigma
        k    = get_max_alevel reduced_nogood a
    in
    (ngs', sigma, k)


  -- return true if the clause is satisfied by the assignment
  is_satisfied c a = 
    let c' = assfromClause c (Ass.length a) in 
    is_sat2 c' a 0



reduceClause :: Clause -> SignedVar -> Clause
-- delete literal from the clause
reduceClause (Clause c w v) (T l) =
--  trace ("reduceNogood: " List.++ (show c) List.++ (show (T l))) $
  let r  = UVec.toList c
      r' = UVec.fromList [ x | x<-r, x/=(l+1) ]
  in
  (Clause r' 0 ((UVec.length r')-1))

reduceClause (Clause c w v) (F l) =
--  trace ("reduceNogood: " List.++ (show c) List.++ (show (F l))) $
  let r  = UVec.toList c
      r' = UVec.fromList [ x | x<-r, x/=(-(l+1)) ]
  in
  (Clause r' 0 ((UVec.length r')-1))



conflict_resolution2 :: NogoodStore -> Clause -> Assignment -> DLT -> (NogoodStore, SignedVar)
conflict_resolution2 ngs nogood a dlt =
--  trace ("conflict_res2: " List.++ (show nogood) List.++ (show a)) $
  let poopi           = assfromClause nogood (Ass.length a)
      (sigma, prefix) = get_implicationLiteral poopi a
      reduced_nogood  = reduceNogood nogood sigma
      alevel_sigma    = get_alevel a sigma 
      dl              = al2dl dlt alevel_sigma
      al              = dl2al dlt dl 
  in
--  trace ("sigma: " List.++ (show sigma)) $
--  trace ("prefix: " List.++ (show prefix)) $
--  trace ("alevel_sigma: " List.++ (show alevel_sigma)) $
--  trace ("dl: " List.++ (show dl)) $
--  trace ("al: " List.++ (show al)) $
  let rhos            = filter_al nogood a al in
--  trace ("  rhos: " List.++ (show rhos)) $
  if only rhos sigma
  then
    let ngs' = add_nogoods [nogood] ngs                                     -- add learned nogood
    in (ngs', sigma)
  else
    let epsilon     = get_antecedent ngs sigma prefix 
        reduced_eps = reduceNogood epsilon (invert sigma) 
        newnogood   = joinClauses reduced_nogood reduced_eps
    in
--    trace ("9: new_nogood:" List.++ (show newnogood)) $
    conflict_resolution2 ngs newnogood prefix dlt



is_sat2 :: Assignment -> Assignment -> Int -> Bool
-- return true if the assignment (c) is subsumed by the assignment a
is_sat2 c a i =
  if i < Ass.length c
  then
    if (a UVec.! i) > 0
    then
      if (c UVec.! i) < 0
      then False
      else is_sat2 c a (i+1)
    else
      if (a UVec.!i) < 0
      then
        if (c UVec.!i) > 0
        then False
        else is_sat2 c a (i+1)
      else -- (a!i) == 0
        if (c UVec.! i) == 0
        then is_sat2 c a (i+1)
        else False
  else True



updatewatch1 :: Int -> Clause -> Assignment -> RES 
updatewatch1 al (Clause c v w) a =
--  trace ("update watch1 ")$
  case new_watch1 (Clause c 0 w) a 0 of
  Just cl -> let w' = c UVec.!w in
             if (a UVec.!((abs w')-1) > 0 && w' > 0) || (a UVec.!((abs w')-1) < 0 && w' < 0) -- assigned
             then updatewatch2x al cl a
             else NIXU cl
  Nothing -> let w'=c UVec.!w in
             if (a UVec.!((abs w')-1) > 0 && w' > 0)                         -- assigned true
             then CONF
             else
               if (a UVec.!((abs w')-1) < 0 && w' < 0)                       -- assigned false
               then CONF
               else
                 if a UVec.!((abs w')-1) == 0
                 then
                   if w' > 0
                   then Res (assign a (F (w'-1)) al)
                   else Res (assign a (T ((abs w')-1)) al)
                 else NIX

updatewatch2 al (Clause c v w) a =
--  trace ("update watch2 ")$
  case new_watch2 (Clause c v 0) a 0 of
  Just cl -> NIXU cl
  Nothing -> let v'=c UVec.!v in
             if a UVec.!((abs v')-1) == 0
             then
               if v' > 0
               then Res (assign a (F (v'-1)) al)
               else Res (assign a (T ((abs v')-1)) al)
             else NIX

updatewatch2x al (Clause c v w) a =
  case new_watch2 (Clause c v 0) a 0 of
  Just cl -> NIXU cl
  Nothing -> let v'=c UVec.!v in
             if a UVec.!((abs v')-1) == 0
             then
               if v' > 0
               then ResU (assign a (F (v'-1)) al) (Clause c v w)
               else ResU (assign a (T ((abs v')-1)) al) (Clause c v w)
             else NIXU (Clause c v w)
  
new_watch1 :: Clause -> Assignment -> Int -> Maybe Clause
new_watch1 (Clause c v w) a i=
--  trace ("new_watch1 " List.++ (show i)) $
  if i < UVec.length c
  then
    let i' = c UVec.!i in
    if i==w
    then new_watch1 (Clause c v w) a (i+1)
    else
      if (a UVec.!((abs i')-1) > 0 && i' >= 0) || (a UVec.!((abs i')-1) < 0 && i' < 0)  -- assigned
      then new_watch1 (Clause c v w) a (i+1)
      else Just (Clause c i w)       
  else Nothing


new_watch2 :: Clause -> Assignment -> Int -> Maybe Clause
new_watch2 (Clause c v w) a i =
--  trace ("new_watch2: " List.++ (show i)) $
  if i < UVec.length c
  then
    let i' = c UVec.!i in
    if i==v
    then new_watch2 (Clause c v w) a (i+1)
    else
      if (a UVec.!((abs i')-1) > 0 && i' > 0) || (a UVec.!((abs i')-1) < 0 && i' < 0)   -- assigned
      then new_watch2 (Clause c v w) a (i+1)
      else Just (Clause c v i)
  else Nothing  

  
fromCClause :: SymbolTable -> CClause -> Clause
fromCClause st (t,f) =
  let l        = BVec.length st
      tsvars   = List.map (get_svarx st) t
      fsvars   = List.map (get_svarx st) f
      tsvars'  = List.map (+1) tsvars
      fsvars'  = List.map (+1) fsvars
      fsvars'' = List.map (*(-1)) fsvars'
      b        = UVec.fromList (tsvars' List.++ fsvars'')
  in
--  trace ("fromCClause: " List.++ (show (t,f)) List.++ (show b)) $
  (Clause b 0 ((UVec.length b) -1))


assfromClause :: Clause -> Int -> Assignment
assfromClause c i = assfromClause2 c (initAssignment i) 0

assfromClause2 :: Clause -> Assignment -> Int -> Assignment
assfromClause2 (Clause c v w) a i =
  if i < UVec.length c
  then
    let i' = c UVec.!i in
    if i' > 0
    then
      let a' = assign a (T (i'-1)) 1 in
      assfromClause2 (Clause c v w) a' (i+1)
    else
      let a' = assign a (F (abs (i')-1)) 1 in
      assfromClause2 (Clause c v w) a' (i+1)
  else a


get_implicationLiteral :: Assignment -> Assignment -> (SignedVar, Assignment)
-- used in conflict_analysis
-- return a implication literal (sigma) from c and a prefix of the assignment a
-- s.t c\prefix = sigma
get_implicationLiteral c a =
--  trace ("get_implicationLiteral: " List.++ (show c) List.++ (show a)) $
  let last_assigned_var = get_last_assigned_var a 
      prefix            = unassign a last_assigned_var
  in
--  trace ("  test: " List.++ (show last_assigned_var)) $
  if (c UVec.!last_assigned_var) /= 0
  then 
    let temp = without c prefix in
--    trace ("   wo: " List.++ (show temp)) $
    if (c UVec.!last_assigned_var) > 0
    then
      let sigma =  (T last_assigned_var) in
      if only temp sigma
      then (sigma, prefix)
      else get_implicationLiteral c prefix
    else
      let sigma =  (F last_assigned_var) in
      if only temp sigma 
      then (sigma, prefix)
      else get_implicationLiteral c prefix
   else get_implicationLiteral c prefix
 


get_last_assigned_var :: Assignment -> SVar
-- get last assigned variable in the assignment
get_last_assigned_var a = get_last_assigned_var2 a 0

get_last_assigned_var2 a i =
  if i < (UVec.length a)
  then
    let val = a UVec.! i in
    case val of
      0 -> get_last_assigned_var2 a (i+1)
      _ -> get_last_assigned_var3 a (i+1) (i, abs val)
  else error "no more assigned variables"

get_last_assigned_var3  a i (akku,akkuval) =
  if i < (UVec.length a)
  then
    let val = a UVec.!i in
    if abs val > akkuval
    then get_last_assigned_var3 a (i+1) (i, abs val)
    else get_last_assigned_var3 a (i+1) (akku,akkuval)
   else akku


get_antecedent :: NogoodStore -> SignedVar -> Assignment -> Clause
-- given an implication literal (sigma) and a prefix return an antecedent (epsilon)
-- s.t. epsilon\prefix = (invert sigma)
get_antecedent ngs sigma prefix =
--    trace ("get_eps: " List.++ (show sigma) List.++ (show prefix)) $ 
  if NGS.can_choose ngs
  then
    let ngs' = choose ngs
        ng   = get_ng ngs'
        temp = reduceNogood ng (invert sigma)
    in
    if is_satisfied temp prefix
    then ng
    else get_antecedent ngs' sigma prefix
  else error "no antecedent epsilon found"


joinClauses :: Clause -> Clause -> Clause
joinClauses (Clause c1 w1 v1) (Clause c2 w2 v2) =
  let c = UVec.fromList $ nub ((UVec.toList c1) List.++ (UVec.toList c2)) in
  (Clause c 0 ((UVec.length c) -1))



without :: Assignment -> Assignment -> Assignment
without c a = without2 c a 0
without2 c a i =
  if i < UVec.length c
  then
    if (c UVec.! i) > 0
    then
      if (a UVec.! i) > 0
      then without2 (c UVec.// [(i,0)]) a (i+1)
        else without2 c a (i+1)
    else
      if (c UVec.! i) < 0
      then
        if (a UVec.! i) < 0
        then without2 (c UVec.// [(i,0)]) a (i+1)
        else without2 c a (i+1)
      else without2 c a (i+1)
  else c


get_max_alevel :: Clause -> Assignment -> Int
-- determin k in conflict_analysis
get_max_alevel (Clause c w v) a = get_max_alevel2 c a 0 0

get_max_alevel2 c a i akku =
--  trace ("get_max_alevel: " List.++ (show c) List.++ (show a) List.++ (show i) List.++ (show akku)) $
  if i < UVec.length c
  then
    let i' = c UVec.! i in
    if a UVec.! ((abs i')-1) > akku
    then get_max_alevel2 c a (i+1) (a UVec.! ((abs i')-1))
    else get_max_alevel2 c a (i+1) akku
  else akku


only :: Assignment -> SignedVar -> Bool
-- returns True if the Signed Literal is the only in the Clause
only c (T l) =
--  trace ("only1 " List.++ (show c) List.++ (show (T l)))  $
  if (c UVec.! l) == 1
  then only2 c l 0
  else False

only c (F l) =
--  trace "only1b"  $
  if (c UVec.! l) == (-1)
  then only2 c l 0
  else False


only2 c l i =
  if i < UVec.length c
  then
    if (c UVec.! i) == 0
    then only2 c l (i+1)
    else
      if l==i
      then  only3 c (i+1)
      else False
  else True

only3 c i =
  if i < UVec.length c
  then
    if (c UVec.! i) == 0
    then only3 c (i+1)
    else False
  else True


filter_al :: Clause -> Assignment -> Int -> Assignment
-- unassigns all literal from c that have in a an alevel < l
filter_al c a l =
--  trace ("filter1: " List.++ (show c) List.++ (show a)) $ 
  let c' = assfromClause c (Ass.length a) in
  filter_al2 c' a l 0

filter_al2 :: Assignment -> Assignment -> Int -> Int -> Assignment
filter_al2 c a l i =
--  trace ("filter2: " List.++ (show c) List.++ (show a)) $ 
  if i < Ass.length c
  then
     if (abs (a UVec.!i)) < l
     then
       let c' = c UVec.// [(i,0)] in
       filter_al2 c' a l (i+1)
     else filter_al2 c a l (i+1)
  else c


