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
   NoGoodStore,
   new_ngs,
   add_nogoods,
   p_nogoods,
   l_nogoods,
   can_choose,
   choose2,
   get_ng,
   up_rew_ngs,
   upgrade_ngs,
   rewind,

) where

import Types

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


can_choose :: NoGoodStore -> Bool
-- returns true if not all nogoods have been tested
can_choose (NoGoodStore png lng pnga lnga counter) = (counter+1) < (length png) + (length lng) 

choose2 :: NoGoodStore -> NoGoodStore
-- is only called if canchoose return true
choose2 (NoGoodStore png lng pnga lnga counter) = (NoGoodStore png lng pnga lnga (counter+1))

