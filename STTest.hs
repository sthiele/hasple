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

module STTest (
   NogoodStore,
   Store,
--    Store,
   new_ngs,
   add_nogoods,
--    get_nogoods,
   can_choose,
   choose,
   get_ng,
   up_rew,
   cupdate,
   rewind,
   Clause,
   fromCClause,
   conflict_resolution,
   RES(..),
   resolve,
) where


--import System.Environment

import Control.Monad.ST
import Data.STRef

import Debug.Trace
import Data.Vector as BVec 
import Data.Vector.Unboxed as UVec
import Data.List


import Assignment as Ass
import SPVar
import DLT

--type Clause = [Int]
--

data RES = Res Assignment
         | ResU Assignment Clause
         | NIX
         | NIXU Clause         
         | CONF
         deriving Show

class (Eq s) => Nogood s where
  resolve :: Int -> s -> Assignment -> RES
  conflict_resolution :: NogoodStore st -> s -> Assignment -> DLT -> ST st (NogoodStore st,SignedVar,Int)
  reduceNogood :: s -> SignedVar -> s
  is_satisfied :: s -> Assignment -> Bool

data Clause = UClause Int
            | BClause Int Int
            | Clause (UVec.Vector Int) {-# UNPACK #-} !Int {-# UNPACK #-} !Int
              deriving (Show,Eq) 


fromCClause :: SymbolTable -> CClause -> Clause
fromCClause st (t,f) =
  let l        = BVec.length st
      tsvars   = Prelude.map (get_svarx st) t
      fsvars   = Prelude.map (get_svarx st) f
      tsvars'  = Prelude.map (+1) tsvars
      fsvars'  = Prelude.map (+1) fsvars
      fsvars'' = Prelude.map (*(-1)) fsvars'
      avars    = tsvars' Prelude.++ fsvars''
      b        = UVec.fromList (avars)
  in
  case Prelude.length avars of
    1 ->
--      trace ("fromCClause: UClause " List.++ (show (t,f)) List.++ (show b)) $
      UClause (Prelude.head avars)
    2 ->
--      trace ("fromCClause: BClause" List.++ (show (t,f)) List.++ (show b)) $
      BClause (Prelude.head avars) (Prelude.head $ Prelude.drop 1 avars)
    _ ->
--      trace ("fromCClause: XClause" List.++ (show (t,f)) List.++ (show b)) $
      (Clause b 0 ((UVec.length b) -1))


-- little helper
get_svarx :: SymbolTable -> SPVar -> SVar
get_svarx st l = get_svar2 l st 0

get_svar2 :: SPVar -> SymbolTable -> Int -> SVar
get_svar2 s st i =
  if st BVec.!i == s
  then i
  else get_svar2 s st (i+1)
  

instance Nogood Clause where

  resolve al (UClause c) a =
--     trace ("res1:") $
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
--     trace ("res2:") $
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
--     trace ("res3:") $
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
  --  trace ("conflict_res1: " Prelude.++ (show nogood) Prelude.++ (show a)) $
  --  trace ("DLT: " Prelude.++ (show alt)) $
    do
      (ngs', sigma) <- (conflict_resolution2 ngs nogood a alt)
--         reduced_nogood  = reduceNogood nogood sigma
--         k    = get_max_alevel reduced_nogood a
--     in
      return $ (ngs', sigma, (get_max_alevel (reduceNogood nogood sigma) a))


  -- return true if the clause is satisfied by the assignment
  is_satisfied c a =
    let c' = assfromClause c (Ass.length a) in
    is_sat2 c' a 0


reduceClause :: Clause -> SignedVar -> Clause
-- delete literal from the clause
reduceClause (UClause c) (T l) =
--  trace ("reduceNogood: " Prelude.++ (show c) Prelude.++ (show (T l))) $
  if c==(l+1)
  then error "empyt clause in reduceClause"
  else (UClause c)

reduceClause (UClause c) (F l) =
--  trace ("reduceNogood: " Prelude.++ (show c) Prelude.++ (show (F l))) $
  if c==(-(l+1))
  then error "empty clause in reduceClause"
  else (UClause c)

reduceClause (BClause x y) (T l) =
--  trace ("reduceNogood: " Prelude.++ (show c) Prelude.++ (show (T l))) $
  if x==(l+1)
  then (UClause y)
  else
    if y==(l+1)
    then (UClause x)
    else (BClause x y)

reduceClause (BClause x y) (F l) =
--  trace ("reduceNogood: " Prelude.++ (show c) Prelude.++ (show (F l))) $
  if x==(-(l+1))
  then (UClause y)
  else
    if y==(-(l+1))
    then (UClause x)
    else (BClause x y)

reduceClause (Clause c w v) (T l) =
--  trace ("reduceNogood: " Prelude.++ (show c) Prelude.++ (show (T l))) $
  let r  = UVec.toList c
      r' = UVec.fromList [ x | x<-r, x/=(l+1) ]
  in
  (Clause r' 0 ((UVec.length r')-1))

reduceClause (Clause c w v) (F l) =
--  trace ("reduceNogood: " Prelude.++ (show c) Prelude.++ (show (F l))) $
  let r  = UVec.toList c
      r' = UVec.fromList [ x | x<-r, x/=(-(l+1)) ]
  in
  (Clause r' 0 ((UVec.length r')-1))







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
--  trace ("new_watch1 " Prelude.++ (show i)) $
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
--  trace ("new_watch2: " Prelude.++ (show i)) $
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

assfromClause :: Clause -> Int -> Assignment
assfromClause (UClause c) i =
    let a = initAssignment i in
    if c > 0
    then
      assign a (T (c-1)) 1
    else
      assign a (F ((abs c)-1)) 1

assfromClause (BClause x y) i =
    let a = initAssignment i in
    if x > 0
    then
      let a' = assign a (T (x-1)) 1 in
      if y > 0
      then assign a' (T (y-1)) 1
      else assign a' (T ((abs y)-1)) 1
    else
      let a' = assign a (F ((abs x)-1)) 1 in
      if y > 0
       then assign a' (T (y-1)) 1
       else assign a' (T ((abs y)-1)) 1

assfromClause c i = assfromClause' c (initAssignment i) 0

assfromClause' :: Clause -> Assignment -> Int -> Assignment
assfromClause' (Clause c v w) a i =
  if i < UVec.length c
  then
    let i' = c UVec.!i in
    if i' > 0
    then
      let a' = assign a (T (i'-1)) 1 in
      assfromClause' (Clause c v w) a' (i+1)
    else
      let a' = assign a (F ((abs i')-1)) 1 in
      assfromClause' (Clause c v w) a' (i+1)
  else a


get_implicationLiteral :: Assignment -> Assignment -> (SignedVar, Assignment)
-- used in conflict_analysis
-- return a implication literal (sigma) from c and a prefix of the assignment a
-- s.t c\prefix = sigma
get_implicationLiteral c a =
--  trace ("get_implicationLiteral: " Prelude.++ (show c) Prelude.++ (show a)) $
  let last_assigned_var = get_last_assigned_var a
      prefix            = unassign a last_assigned_var
  in
--  trace ("  test: " Prelude.++ (show last_assigned_var)) $
  if (c UVec.!last_assigned_var) /= 0
  then
    let temp = without c prefix in
--    trace ("   wo: " Prelude.++ (show temp)) $
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


only :: Assignment -> SignedVar -> Bool
-- returns True if the Signed Literal is the only in the Clause
only c (T l) =
--  trace ("only1 " Prelude.++ (show c) Prelude.++ (show (T l)))  $
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
--  trace ("filter1: " Prelude.++ (show c) Prelude.++ (show a)) $
  let c' = assfromClause c (Ass.length a) in
  filter_al2 c' a l 0

filter_al2 :: Assignment -> Assignment -> Int -> Int -> Assignment
filter_al2 c a l i =
--  trace ("filter2: " Prelude.++ (show c) Prelude.++ (show a)) $
  if i < Ass.length c
  then
     if (abs (a UVec.!i)) < l
     then
       let c' = c UVec.// [(i,0)] in
       filter_al2 c' a l (i+1)
     else filter_al2 c a l (i+1)
  else c

get_max_alevel :: Clause -> Assignment -> Int
-- determin k in conflict_analysis
get_max_alevel (UClause c) a =
  abs (a UVec.! ((abs c)-1))

get_max_alevel (BClause x y) a =
  let alx = abs (a UVec.! ((abs x)-1))
      aly = abs (a UVec.! ((abs y)-1))
  in
  if alx > aly
  then alx
  else aly

get_max_alevel (Clause c w v) a = get_max_alevel' c a 0 0

get_max_alevel' c a i akku =
--  trace ("get_max_alevel: " Prelude.++ (show c) Prelude.++ (show a) Prelude.++ (show i) Prelude.++ (show akku)) $
  if i < UVec.length c
  then
    let i'   = c UVec.! i
        ali' = abs (a UVec.! ((abs i')-1))
    in
    if ali' > akku
    then get_max_alevel' c a (i+1) (ali')
    else get_max_alevel' c a (i+1) akku
  else akku




joinClauses :: Clause -> Clause -> Clause
joinClauses (Clause c1 w1 v1) (Clause c2 w2 v2) =
  let c = UVec.fromList $ nub ((UVec.toList c1) Prelude.++ (UVec.toList c2)) in
  (Clause c 0 ((UVec.length c) -1))

  
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


data Store s = Store { refs    :: [(STRef s Clause)],
                       counter :: Int
                     }

type NogoodStore s = Store s 

mkStore :: [Clause] -> ST s (Store s)
mkStore x  = 
  do
    refs <- Prelude.mapM newSTRef x
    return $ (Store refs (-1))

new_ngs :: [Clause] -> [Clause] -> ST s (Store s)
-- create a new store
new_ngs png lng =
  do
    r_png <- Prelude.mapM newSTRef png
    r_lng <- Prelude.mapM newSTRef lng
    return $ (Store (r_png Prelude.++ r_lng) (-1))


cupdate :: Store s  -> Clause -> ST s ()
-- replace current nogood with new nogood reset nogood store
cupdate st cl =
  do
    modifySTRef (current st) (\x -> cl)


rewind :: Store s -> Store s
-- basically reset the nogood store because some resolvent was found
rewind (Store png counter) = (Store png (-1))

    
up_rew :: Store s -> Clause -> ST s (Store s)
-- update and rewind
up_rew (Store ngs c) cl =
  do 
    modifySTRef (current (Store ngs c)) (\x -> cl)
    return $ (Store ngs (-1))


shead :: Store s -> STRef s Clause
shead (Store (x:xs) c) = x
tolist (Store x c) = x

current (Store x c) =
--   trace ("getng" Prelude.++ (show c)) $
  x!!c

can_choose (Store x c) = c < ((Prelude.length x) -1)


choose (Store x c) =
--   trace ("choose") $
  (Store x (c+1))

addClause :: Store s -> Clause -> ST s (Store s)
addClause (Store st c) x =
  do 
    rx <- newSTRef x
--     return $ (Store (rx:st) (c+1)) -- prepend
    return $ (Store (st Prelude.++ [rx]) c) -- append

add_nogoods :: Store s -> [Clause] -> ST s (Store s)
add_nogoods (Store st c) x =
  do
    refs <- Prelude.mapM newSTRef x
--    return $ (Store (refs Prelude.++ st) (c+(Prelude.length x))) -- prepend
    return $ (Store (st Prelude.++ refs) c) -- append

get_ng = current



next :: Store s ->  ST s (Store s)
next (Store st c) = 
  do
    if c < Prelude.length st
    then return $ (Store st (c+1))
    else return $ (Store st 0)



conflict_resolution2 :: Store s -> Clause -> Assignment -> DLT -> ST s (Store s, SignedVar)
conflict_resolution2 ngs nogood a dlt =
  let poopi           = assfromClause nogood (Ass.length a)
      (sigma, prefix) = get_implicationLiteral poopi a
      reduced_nogood  = reduceNogood nogood sigma
      alevel_sigma    = get_alevel a sigma
      dl              = al2dl dlt alevel_sigma
      al              = dl2al dlt dl
  in
  let rhos            = filter_al nogood a al in
  if only rhos sigma
  then
    do ngs' <- add_nogoods ngs [nogood]                                     -- add learned nogood
       return $ (ngs', sigma)
  else
  do
    epsilon     <- get_antecedent ngs sigma prefix
--     let
--         epsilon     = get_antecedent ngs sigma prefix
    let reduced_eps = reduceNogood epsilon (invert sigma)
    let newnogood   = joinClauses reduced_nogood reduced_eps
--     in
--     do 
    conflict_resolution2 ngs newnogood prefix dlt


get_antecedent :: Store s -> SignedVar -> Assignment -> ST s Clause
-- given an implication literal (sigma) and a prefix return an antecedent (epsilon)
-- s.t. epsilon\prefix = (invert sigma)
get_antecedent ngs sigma prefix =
--    trace ("get_eps: " Prelude.++ (show sigma) Prelude.++ (show prefix)) $
  
    if can_choose ngs
    then
      let ngs' = choose ngs
          ng   = get_ng ngs'
      in
      do
        vng <- readSTRef ng
        if is_satisfied (reduceNogood vng (invert sigma)) prefix
        then return vng
        else get_antecedent ngs' sigma prefix
    else error "no antecedent epsilon found"






s_new_watch1 :: Clause -> Assignment -> Int -> Store s -> ST s ()
s_new_watch1 (Clause c v w) a i st =
  do
    if i < UVec.length c
    then
      let i' = c UVec.!i in
      if i==w
      then s_new_watch1 (Clause c v w) a (i+1) st
      else
        if (a UVec.!((abs i')-1) > 0 && i' >= 0) || (a UVec.!((abs i')-1) < 0 && i' < 0)  -- assigned
        then s_new_watch1 (Clause c v w) a (i+1) st
        else modifySTRef (current st) (\x -> Clause c i w) --Just (Clause c i w)   
    else return ()

--foo :: 

foo x  =
  let ass = initAssignment 10 
  in 
  runST $ do
    st <- mkStore x
    now <- readSTRef  (current st)
    s_new_watch1 now ass 1 $ st
    st'  <-  addClause st (UClause 1)
    st'' <- next st'
    vals <- Prelude.mapM readSTRef (tolist st'')
    return vals




main :: IO ()
main =
  let x = [(Clause (UVec.fromList [1,2,3,4,5]) 0 4),(UClause 2),(UClause 3),(UClause (-4)),(BClause 2 3)] 
  in
  do
    putStrLn $ show x
    putStrLn $ show (foo x)
