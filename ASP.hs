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

module ASP (
    Term(..), Atom(..), __conflict, Rule(..), anssets, findas, sol, ground_program,
  ) where
  
import Data.List (sort, nub)
-- import Data.List.Extra (nubOrd)
-- use sort to order list nub (nubOrd) to remove duplicates from list -- maybe use Sets instead?
import qualified Data.Set as Set
import qualified Data.Map as Map

                    
 
--my showlist 
showlist :: (Show a) => [a] -> String
showlist [] = ""
showlist (x:[]) = (show x)
showlist (x:xs) = (show x)  ++ "," ++ (showlist xs)


-- ########################################

data Term = Constant Int
                | Identifier String
                | Variable String
                | Addition Term Term
                | Subtraction Term Term
                | Multiplication Term Term
--                 | Division Term Term
                | Negation Term
                deriving (Eq, Ord)
                
instance Show Term where
  show (Identifier x) = x
  show (Variable x) = x
  show (Constant x) = show x

  
-- --------------------------------------------------------------

data Atom = Atom { predicate :: String
                 , arguments :: [Term]
                 }
                 
instance Show Atom where
    show (Atom pred []) =  pred
    show (Atom pred xs) =  pred ++"("++showlist xs++")"
    
instance Eq Atom where
  (Atom p1 args1) == (Atom p2 args2) = p1==p2 && args1==args2

instance Ord Atom where
  compare (Atom pred args) (Atom pred2 args2) = compare pred pred2

  
-- --------------------------------------------------------------

data Rule = Rule { kopf :: Atom
                 , pbody :: [Atom]
                 , nbody :: [Atom]
                 }

shownbody :: [Atom] -> String
shownbody [] = ""
shownbody (x:[]) = "not " ++ (show x)
shownbody (x:xs) =  "not " ++ (show x) ++ ", "++ (shownbody xs)

instance Show Rule where
  show (Rule h [] []) =  (show h) ++"."
  show (Rule h pb []) =  (show h) ++ " :- "++showlist pb++"."
  show (Rule h [] nb) =  (show h) ++ " :- "++shownbody nb++"."
  show (Rule h pb nb) =  (show h) ++ " :- "++(showlist pb)++", "++(shownbody nb)++"."

instance Eq Rule where
  (Rule h1 pb1 nb1) == (Rule h2 pb2 nb2) = h1==h2 && pb1==pb2 && nb1==nb2

instance Ord Rule where
  compare (Rule h pb nb) (Rule h2 pb2 nb2) = compare h h2

          
-- --------------------------------------------------------------                


-- type MapOfSets =  Map.Map (String, Int) (Set.Set Atom)
type MapOfSets =  Map.Map (String, Int) (Set.Set [Term])     

-- insert_mos:: MapOfSets -> Atom -> MapOfSets
insert_mos:: MapOfSets -> (String, Int) -> [Term] -> MapOfSets      
insert_mos mos key val = 
    case Map.lookup key mos of 
      Nothing -> if (allconst val)
                    then Map.insert key (Set.insert val Set.empty) mos
                    else mos
      Just x  -> if (allconst val)
                    then Map.insert key (Set.insert val x) mos
                    else mos


allconst:: [Term] -> Bool
allconst [] = True
allconst ((Identifier x):xs) = True && allconst xs
allconst ((Constant x):xs) = True && allconst xs
allconst _ = False


      
--TODO rename to get mos      
getpredval:: [Atom] -> MapOfSets
getpredval [] = Map.empty
getpredval ((Atom pred args):xs) = insert_mos (getpredval xs) (pred, (length args)) args



-- can two terms be unified if yes return variable bindings
matchTerm:: Term -> Term -> Maybe [(Term,Term)]
matchTerm (Identifier x) (Constant y) = Nothing
matchTerm (Constant x) (Identifier y) = Nothing
matchTerm (Constant x) (Constant y) =
  if x==y
     then Just []
     else Nothing
matchTerm (Identifier x) (Identifier y) =
  if x==y
     then Just []
     else Nothing

matchTerm (Variable x) (Identifier y) = Just [ ((Variable x),(Identifier y))]
matchTerm (Variable x) (Constant y) = Just [ ((Variable x),(Constant y))]
matchTerm (Addition x y) (Constant z) = Just []
matchTerm (Addition x y) (Identifier z) = Nothing
matchTerm (Subtraction x y) (Constant z) = Just []
matchTerm (Subtraction x y) (Identifier z) = Nothing
matchTerm (Multiplication x y) (Constant z) = Just []
matchTerm (Multiplication x y) (Identifier z) = Nothing
matchTerm (Negation x) (Constant z) = Just []
matchTerm (Negation x) (Identifier z) = Nothing
matchTerm (Variable x) (Variable y) = Just [((Variable x),(Variable y))]
matchTerm x y = Just [(x,(Identifier ("Whaaat????"++ show y)))]




-- can two argumentlist be unified if yes return variable bindings
match:: [Term] -> [Term] -> Maybe [(Term,Term)]
match [] [] = Just []
match (x:xs) (y:ys) = 
  if (length xs) == (length ys) 
     then 
     case (matchTerm x y) of
          Nothing -> Nothing
          Just [] ->  (match xs ys)     
          Just [(var,const)] -> join (var,const) (match xs ys)
     else Nothing
     

join:: (Term,Term) -> Maybe [(Term,Term)] -> Maybe [(Term,Term)]
join x Nothing = Nothing
join x (Just []) = Just [x]
join (v, c) (Just list) = 
      case lookup v list of
           Nothing -> (Just ((v,c):list))
           Just x -> if x==c 
                        then Just list
                        else Nothing



-- return the possible variable bindings associated a non ground atom
getbindings:: Atom -> MapOfSets -> [[(Term,Term)]]
getbindings  (Atom pred args) m = 
  let x = Map.lookup (pred, (length args)) m in
      case x of
           Nothing -> [[]]
           Just z ->  (getbindings2 args (Set.toList z))

-- getbindings2:: [Term] -> [Atom] ->  [[(Term,Term)]]
getbindings2:: [Term] -> [[Term]] ->  [[(Term,Term)]]
getbindings2 x [] = []
getbindings2 x (y:ys) = 
  case (match x y) of
       Nothing -> (getbindings2 x ys)
       Just z -> z:(getbindings2 x ys)
       
       
getbindingsAtoms:: [Atom] -> MapOfSets -> [[(Term,Term)]]
getbindingsAtoms [] m = [[]]
getbindingsAtoms (x:xs) m = join2 (getbindings x m) (getbindingsAtoms xs m)

join2:: [[(Term,Term)]] -> [[(Term,Term)]] -> [[(Term,Term)]]
-- join2 xs ys = [ z | x <- xs, y <- ys, (merge x y)==(Just z)]
join2 [] ys = []
join2 xs [] = []
join2 xs ys =
  do 
    x <- xs
    y <- ys
    case (merge x y) of
         Just z -> return z
         Nothing -> [] 
         
                                   
merge:: [(Term,Term)] -> [(Term,Term)] -> Maybe [(Term,Term)]
merge [] ys = Just ys
merge (x:xs) ys = 
  case (merge2 x ys) of
       Nothing -> Nothing
       Just z -> merge xs z
       
 
merge2:: (Term,Term) -> [(Term,Term)] -> Maybe [(Term,Term)]
merge2 (k,v) ys = 
  case lookup k ys of
       Nothing -> Just ((k,v):ys)
       Just z -> if v==z
                    then (Just ys)
                    else Nothing

   
-- --------------------------------------------------------------

subsTerm:: [(Term,Term)] -> Term -> Term
-- subsTerm:: Map.Map Term Term -> Term -> Term
subsTerm m (Constant x) = (Constant x)
subsTerm m (Identifier x) = (Identifier x)
subsTerm m (Variable x) =
              case lookup (Variable x) m of
                Just y -> y
                Nothing -> (Variable x)
                
subsTerm m (Addition x y) =
              let xsubs = subsTerm m x
                  ysubs = subsTerm m y
              in (Addition xsubs ysubs)

subsTerm m (Subtraction x y) =
              let xsubs = subsTerm m x
                  ysubs = subsTerm m y
              in (Subtraction xsubs ysubs)
              
subsTerm m (Multiplication x y) =
              let xsubs = subsTerm m x
                  ysubs = subsTerm m y
              in (Multiplication xsubs ysubs)
              
subsTerm m (Negation x) =
              let xsubs = subsTerm m x
              in (Negation xsubs)
              
              

subsAtom:: [(Term,Term)] -> Atom -> Atom
-- subsAtom:: Map.Map Term Term -> Atom -> Atom
subsAtom m (Atom pred []) = (Atom pred [])
subsAtom m (Atom pred x)  = (Atom pred (map (subsTerm m) x))

ground_rule:: Rule -> [(Term,Term)] -> Rule
ground_rule (Rule h pb nb) m= (Rule (subsAtom m h) (map (subsAtom m) pb) (map (subsAtom m) nb))

ground_rules:: [[(Term,Term)]] ->  Rule -> [Rule]
ground_rules xs r = map (ground_rule r) xs

-- alternative
ground_rules2:: MapOfSets ->  Rule -> [Rule]
ground_rules2 m (Rule h pb nb) =
  let c =  getbindingsAtoms pb m
  in  nub (map (ground_rule (Rule h pb nb)) c)


ground_program:: [Rule] -> [Rule]
ground_program p =
  let m = getpredval (heads_p  p)
      pg1 = nub (concatMap  (ground_rules2 m)  p)
  in
    if pg1==p
       then pg1
       else ground_program pg1
      


      
ac = (Atom "a" [(Identifier "c")])
av = (Atom "a" [(Variable "X")])

bv = (Atom "b" [(Variable "X")])

rv = (Atom "r" [(Variable "X")])
rc = (Atom "r" [(Identifier "x")])


mm = getpredval [rc]
mr = (Rule __conflict [rv] [])

mp = [
        (Rule ac [] []),
        (Rule rv [av] [bv]),
        mr
      ]
-- --------------------------------------------------------------


__conflict = (Atom "conflict" [])


heads_p :: [Rule] -> [Atom]
-- returns the head of all rules without the contradiction symbol "" (all consistent consequences)
heads_p rules = filter (\i -> i/=__conflict ) (nub (map kopf rules))


subsets :: [a] -> [[a]]
subsets []  = [[]]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)


reducepbody :: [Atom] -> [Atom] -> [Atom]
-- reduces a positive body
reducepbody x y = [a | a <- x, not( a `elem` y)]


reducenbody :: [Atom] -> [Atom] -> [Atom]
-- reduces the negative body
reducenbody x y = [a | a <- x, a `elem` y]


facts :: [Rule] -> [Atom]
-- return the facts of a programm
facts p = [ (kopf r) |  r <- p,  (null (pbody r)), (null (nbody r)) ]


reducebasicprogram :: [Rule] -> [Atom] -> [Rule]
reducebasicprogram p x = [ (Rule (kopf r) (reducepbody (pbody r) x) []) | r <- p, (pbody r)/=[] ]


cn :: [Rule] -> [Atom]
-- return the consequences of a  basic logic programm
cn [] = []
cn p = if (reducebasicprogram p (facts p)) == p
   then (facts p)
   else nub ((facts p) ++ (cn (reducebasicprogram p (facts p))))


reduct :: [Rule] -> [Atom] -> [Rule]
-- return the reduct of a logic program with x
reduct p x = [ (Rule (kopf r) (pbody r) []) |  r <- p,  (reducenbody (nbody r) x)==[] ]


anssets p = filter (\i -> (sort (cn (reduct p i)))==(sort i)) (subsets (heads_p p))




data Answer = SAT [[Atom]] | UNSAT [Atom]

instance Show Answer where
  show (SAT x) =  "SAT: " ++ show x
  show (UNSAT x)   =  "UNSAT: " ++ show x


sol :: Answer -> [[Atom]]
sol (UNSAT s) = []
sol (SAT s) = s


-- given a list of boolean Variables returns all possible interpretations
assignment_generator c = (subsets c)

-- test whether cond is satified by candidate
-- tester for an answer set
test:: [Rule] -> [Atom] -> Bool
test p candidate = (sort (cn (reduct p candidate)))==(sort candidate)


-- choose heuristic
-- use info to reorder the candidates such that the most prefered is first
choose:: [a] -> info -> [a]
-- very stupid heuristic
choose x info = x

findas:: [Rule] -> Int -> Answer
-- return atmost n answer sets for program p
findas p n =
  let variables= (heads_p p)
  in check p (assignment_generator variables) n

check:: [Rule] -> [[Atom]] -> Int -> Answer
check cond [] num = UNSAT [__conflict]
check cond candidates num=
  let choice = head candidates in
  if (test cond choice)
  then
    if (num==1)
    then SAT [choice]
    else
      --    learn answer
      SAT (choice: sol (check cond (tail candidates) (num-1)))
  else
    --    let conflicts=conflictana
    check cond (tail candidates) (num)


r = (Atom "r" [])
p = (Atom "p" [])
q = (Atom "q" [])

p1 = [ (Rule q [] []),
       (Rule p [q] [r]) ]
       

p2 = [ (Rule q [] []),
       (Rule p [p] [r]) ]

p3 = [ (Rule p [] [q]),
       (Rule q [] [p]) ]

p4 = [ (Rule p [] [p])]

p5 = [ (Rule p [] [q,r]),
       (Rule q [] [p,r]),
       (Rule r [] [p,q]),
       (Rule __conflict [r] []),
       (Rule p [] [q,r])
       ]






