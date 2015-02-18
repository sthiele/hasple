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
    Term, constant, variable, Atom(..), __conflict, Rule(..), anssets, findas, sol, ground_program,
  ) where
  
import Data.List (sort, nub)
-- import Data.List.Extra (nubOrd)
-- use sort to order list nub (nubOrd) to remove duplicates from list -- maybe use Sets instead?
import qualified Data.Set as Set
import qualified Data.Map as Map


-- | /O(n log n)/. The 'nubOrd' function removes duplicate elements from a list.
-- In particular, it keeps only the first occurrence of each element.
-- Unlike the standard 'nub' operator, this version requires an 'Ord' instance
-- and consequently runs asymptotically faster.
--
-- > nubOrd "this is a test" == "this ae"
-- > nubOrd (take 4 ("this" ++ undefined)) == "this"
-- > \xs -> nubOrd xs == nub xs
nubOrd :: Ord a => [a] -> [a]
nubOrd = nubOrdBy compare

-- | A version of 'nubOrd' with a custom predicate.
--
-- > nubOrdBy (compare `on` length) ["a","test","of","this"] == ["a","test","of"]
nubOrdBy :: (a -> a -> Ordering) -> [a] -> [a]
nubOrdBy cmp xs = f E xs
  where f seen [] = []
        f seen (x:xs) | memberRB cmp x seen = f seen xs
                      | otherwise = x : f (insertRB cmp x seen) xs

---------------------------------------------------------------------
-- OKASAKI RED BLACK TREE
-- Taken from http://www.cs.kent.ac.uk/people/staff/smk/redblack/Untyped.hs

data Color = R | B deriving Show
data RB a = E | T Color (RB a) a (RB a) deriving Show

{- Insertion and membership test as by Okasaki -}
insertRB :: (a -> a -> Ordering) -> a -> RB a -> RB a
insertRB cmp x s =
    T B a z b
    where
    T _ a z b = ins s
    ins E = T R E x E
    ins s@(T B a y b) = case cmp x y of
        LT -> balance (ins a) y b
        GT -> balance a y (ins b)
        EQ -> s
    ins s@(T R a y b) = case cmp x y of
        LT -> T R (ins a) y b
        GT -> T R a y (ins b)
        EQ -> s

memberRB :: (a -> a -> Ordering) -> a -> RB a -> Bool
memberRB cmp x E = False
memberRB cmp x (T _ a y b) = case cmp x y of
    LT -> memberRB cmp x a
    GT -> memberRB cmp x b
    EQ -> True

{- balance: first equation is new,
   to make it work with a weaker invariant -}
balance :: RB a -> a -> RB a -> RB a
balance (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
balance (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance a x b = T B a x b

                      
 
--my showlist 
showlist :: (Show a) => [a] -> String
showlist [] = ""
showlist (x:[]) = (show x)
showlist (x:xs) = (show x)  ++ "," ++ (showlist xs)


-- ########################################

data Term = Term { is_const :: Bool
                 , name :: String
                 }
-- data Val =  String | Int
                 
constant:: String -> Term
constant x = (Term True x)

variable :: String -> Term
variable x = (Term False x)

instance Show Term where
  show (Term True x) =  show x
  show (Term False x) = x

instance Ord Term where
  compare (Term True args) (Term False args2) = compare True  False
  compare (Term False args) (Term True args2) = compare False True
  compare (Term True args) (Term True args2) = compare args args2
  compare (Term False args) (Term False args2) = compare args args2

instance Eq Term where
  (Term b1 args1) == (Term b2 args2) = b1==b2 && args1==args2

  
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
      Nothing -> Map.insert key (Set.insert val Set.empty) mos
      Just x  -> Map.insert key (Set.insert val x) mos

      
--TODO rename to get mos      
getpredval:: [Atom] -> MapOfSets
getpredval [] = Map.empty
getpredval ((Atom pred args):xs) = insert_mos (getpredval xs) (pred, (length args)) args



matchTerm:: Term -> Term -> Maybe [(Term,Term)]
matchTerm (Term True x) (Term True y) = 
  if x==y 
     then Just []
     else Nothing
matchTerm (Term False x) (Term True y) = Just [ ((Term False x),(Term True y))]
matchTerm (Term False x) (Term False y) = Just []
matchTerm (Term True x) (Term False y) = Nothing


match:: [Term] -> [Term] -> Maybe [(Term,Term)]
match [] [] = Just []
match (x:xs) (y:ys) = 
  if (length xs) == (length ys) 
     then 
     case (matchTerm x y) of
          Nothing -> Nothing
          Just [] ->  (match xs ys)     
          Just [((Term False x),(Term True y))] -> join ((Term False x),(Term True y)) (match xs ys)
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
                    


getbindings:: Atom -> MapOfSets -> [[(Term,Term)]]
getbindings  (Atom pred args) m = 
  let x = Map.lookup (pred, (length args)) m in
      case x of
           Nothing -> []
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

   

   
arg1 = [ (constant "a"), (constant "a"), (constant "c")]
arg2 = [ (constant "a"), (constant "b"), (constant "e")]
arg3 = [ (constant "b"), (constant "c"), (constant "d")]
arg4 = [ (constant "a"), (constant "c"), (constant "e")]
arg5 = [ (constant "c"), (constant "b"), (constant "a")]

arg6 = [ (constant "a"), (constant "b")]
arg7 = [ (constant "a"), (constant "a")]
arg8 = [ (constant "b"), (constant "c")]
arg9 = [ (constant "a"), (constant "e")]
arg10 = [ (constant "c"), (constant "b")]


arg11 = [ (variable "X"), (constant "b"), (constant "c")]
arg12 = [ (variable "X"), (variable "X"), (constant "c")]
arg13 = [ (variable "X"), (variable "Y"), (constant "e")]


a1 = (Atom "a" arg1)
a2 = (Atom "a" arg2)
a3 = (Atom "a" arg3)
a4 = (Atom "a" arg5)
a5 = (Atom "a" arg6)
a6 = (Atom "a" arg9)
a7 = (Atom "a" arg10)

a8 = (Atom "a" arg12)
a9 = (Atom "a" arg13)

b1 = (Atom "b" arg1)
b2 = (Atom "b" arg2)
b3 = (Atom "b" arg4)
b4 = (Atom "b" arg6)
b5 = (Atom "b" arg7)
b6 = (Atom "b" arg8)
b7 = (Atom "b" arg10)

b8 = (Atom "b" arg11)
b9 = (Atom "b" arg13)


mos1 = getpredval [a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7]       

mySubs1 = getbindings a8 mos1  
mySubs2 = getbindings a9 mos1  
mySubs3 = getbindings b8 mos1  
mySubs4 = getbindings b9 mos1  

mySubsx = getbindingsAtoms [a8,a9,b9] mos1  
mySubsy = getbindingsAtoms [a8,a9,b8,b9] mos1



-- --------------------------------------------------------------

subsTerm:: [(Term,Term)] -> Term -> Term
-- subsTerm:: Map.Map Term Term -> Term -> Term
subsTerm m (Term True x) = (Term True x)
subsTerm m x =
              case lookup x m of
                Just y -> y
                Nothing -> x

subsAtom:: [(Term,Term)] -> Atom -> Atom
-- subsAtom:: Map.Map Term Term -> Atom -> Atom
subsAtom m (Atom pred []) = (Atom pred [])
subsAtom m (Atom pred x)  = (Atom pred (map (subsTerm m) x))

ground_rule:: Rule -> [(Term,Term)] -> Rule
ground_rule (Rule h pb nb) m= (Rule (subsAtom m h) (map (subsAtom m) pb) (map (subsAtom m) nb))

ground_rules:: [[(Term,Term)]] ->  Rule -> [Rule]
ground_rules xs r = map (ground_rule r) xs

-- alterantive
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
      

ay = (Atom "a" [(variable "Y")])
uv = (Atom "u" [(variable "X")])
tv = (Atom "t" [(variable "X")])
sv = (Atom "s" [(variable "X")])
rv = (Atom "r" [(variable "X")])
pv = (Atom "p" [(variable "X")])
qv = (Atom "q" [(variable "X")])
qc = (Atom "q" [(constant "c")])
qc2 = (Atom "q" [(constant "k")])


pv1 = [
        (Rule qc [] []),
        (Rule qc2 [] []),
        (Rule pv [qv] [ay]),
        (Rule rv [pv] []),
        (Rule sv [rv] []),
        (Rule tv [uv] [])
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


-- given a list of boolean variables returns all possible interpretations
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






