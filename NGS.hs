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
   choose,
   get_ng,
   up_rew,
   upgrade,
   rewind,

) where

import Types
import Data.Vector as Vector

data NoGoodStore = NoGoodStore { program_nogoods :: Vector Clause -- program nogoods
                               , learned_nogoods :: Vector Clause -- learned nogoods
                               , png_akku        :: [Clause] -- program nogoods akku
                               , lng_akku        :: [Clause] -- learned nogoods akku
                               , counter         :: Int
} deriving (Show, Eq)


new_ngs :: [Clause] -> [Clause] -> NoGoodStore
new_ngs png lng = NoGoodStore (fromList png) (fromList lng) [] [] (-1)


ngs_size :: NoGoodStore -> Int
ngs_size (NoGoodStore png lng _ _ _) = (Vector.length png) + (Vector.length lng)


p_nogoods ngs = (toList (program_nogoods ngs)) Prelude.++ (png_akku ngs)
l_nogoods ngs = (toList (learned_nogoods ngs)) Prelude.++ (lng_akku ngs)


get_ng :: NoGoodStore -> Clause
-- get current nogood
get_ng (NoGoodStore png lng _ _ counter) =
  let len_png = Vector.length png in
  if counter < len_png
  then png!counter
  else
    if counter < (len_png) + (Vector.length lng)
    then lng!(counter-len_png)
    else error "NoGoodStore out of bounds"


add_nogoods :: [Clause] -> NoGoodStore -> NoGoodStore
add_nogoods ngs (NoGoodStore png lng pnga lnga c) =
  (NoGoodStore png (lng Vector.++(fromList ngs)) pnga lnga c) 


rewind :: NoGoodStore -> NoGoodStore
-- basically reset the nogood store because some resolvent was found
rewind (NoGoodStore png lng pnga lnga counter) =
  if counter < Vector.length png
  then 
    let png' = png Vector.++ (fromList pnga) in
    (NoGoodStore png' lng [] [] (-1))
  else
    let png' = png Vector.++ (fromList pnga)
        lng' = lng Vector.++ (fromList lnga) 
    in
    NoGoodStore png' lng' [] [] (-1)


upgrade :: NoGoodStore -> Clause -> NoGoodStore
-- replace current nogood with new nogood reset nogood store
upgrade (NoGoodStore png lng pnga lnga counter) ng =
  let len_png = Vector.length png in
  if counter < len_png
  then 
    let png'  = Vector.drop (counter+1) png
        pnga' = (toList (Vector.take counter png)) Prelude.++ (ng:pnga) 
    in
    (NoGoodStore png' lng pnga' lnga (-1))
  else
    let png'  = fromList []
        pnga' = (toList png) Prelude.++  pnga
        lng'  = Vector.drop (counter+1-len_png) lng
        lnga' = (toList (Vector.take (counter-len_png) lng)) Prelude.++(ng:lnga) 
    in
    NoGoodStore png' lng' pnga' lnga' (-1)


up_rew :: NoGoodStore -> Clause -> NoGoodStore
-- upgrade and rewind
up_rew (NoGoodStore png lng pnga lnga counter) ng =
  let len_png = Vector.length png in
  if counter < len_png
  then 
    let png' = snoc ((Vector.take counter png) Vector.++ (Vector.drop (counter+1) png) Vector.++ (fromList pnga)) ng in
    (NoGoodStore png' lng [] [] (-1))
  else
    let png' = png Vector.++(fromList pnga)
        lng' = snoc ((Vector.take (counter-len_png) lng) Vector.++ (Vector.drop (counter+1-len_png) lng) Vector.++ (fromList lnga)) ng
    in
    (NoGoodStore png' lng' [] [] (-1))


can_choose :: NoGoodStore -> Bool
-- returns true if not all nogoods have been tested
can_choose (NoGoodStore png lng pnga lnga counter) = (counter+1) < (Vector.length png) + (Vector.length lng) 

choose :: NoGoodStore -> NoGoodStore
-- is only called if canchoose return true
choose (NoGoodStore png lng pnga lnga counter) = (NoGoodStore png lng pnga lnga (counter+1))

