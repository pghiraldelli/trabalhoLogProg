module DPLL

where 

import Data.List

type Clause    = [Integer]
type ClauseSet = [Clause]

type Valuation = [Integer]

rSort :: ClauseSet -> ClauseSet
rSort = (srt1.nub) . (map (srt2. nub)) 
  where srt1 = sortBy cmp
        cmp [] (_:_)  = LT 
        cmp [] []     = EQ
        cmp (_:_) []  = GT
        cmp (x:xs) (y:ys) | (abs x) < (abs y)  = LT
                          | (abs x) > (abs y)  = GT 
                          | (abs x) == (abs y) = cmp xs ys
        srt2 = sortBy (\ x y -> compare (abs x) (abs y))

trivialC :: Clause -> Bool
trivialC [] = False
trivialC (i:is) = elem (-i) is || trivialC is

clsNub :: ClauseSet -> ClauseSet 
clsNub = filter (not.trivialC) 

data Trie = Nil | End | Tr Integer Trie Trie Trie deriving (Eq,Show)

nubT :: Trie -> Trie
nubT (Tr v p n End)   = End
nubT (Tr v End End r) = End
nubT (Tr v Nil Nil r) = r
nubT tr               = tr

trieMerge :: Trie -> Trie -> Trie 
trieMerge End _ = End
trieMerge _ End = End
trieMerge t1 Nil = t1
trieMerge Nil t2 = t2
trieMerge t1@(Tr v1 p1 n1 r1) t2@(Tr v2 p2 n2 r2) 
  | v1 == v2 = (Tr 
                v1 
                (trieMerge p1 p2) 
                (trieMerge n1 n2) 
                (trieMerge r1 r2) 
                )
  | v1 < v2 = (Tr 
                v1 
                p1 
                n1 
                (trieMerge r1 t2)
                )
  | v1 > v2 = (Tr 
                v2 
                p2 
                n2 
                (trieMerge r2 t1)
                )

cls2trie :: ClauseSet -> Trie
cls2trie []             = Nil
cls2trie ([]:_)         = End
cls2trie cls@((i:is):_) = 
  let j = abs i in 
   (Tr
    j
    (cls2trie [ filter (/= j)  cl | cl <- cls, elem   j  cl ])
    (cls2trie [ filter (/= -j) cl | cl <- cls, elem (-j) cl ])
    (cls2trie [ cl | cl <- cls, notElem j cl, notElem (-j) cl ])
   )

trie2cls :: Trie -> ClauseSet
trie2cls Nil = []
trie2cls End = [[]]
trie2cls (Tr i p n r) = 
    [ i:rest | rest <- trie2cls p ]
    ++
    [ (-i):rest | rest <- trie2cls n ] 
    ++ 
    trie2cls r

units :: Trie -> [Integer]
units Nil  = []
units End  = []
units (Tr i End n r) = i : units r
units (Tr i p End r) = -i: units r 
units (Tr i p n r)     = units r

unitProp :: (Valuation,Trie) -> (Valuation,Trie)
unitProp (val,tr) = (nub (val ++ val'), unitPr val' tr) 
  where 
  val' = units tr
  unitPr :: Valuation -> Trie -> Trie
  unitPr [] tr = tr
  unitPr (i:is) tr = unitPr is (unitSR i tr) 

unitSR :: Integer -> Trie -> Trie 
unitSR i = (unitR pol j) . (unitS pol j) 
  where pol = i>0
        j   = abs i

unitS :: Bool -> Integer -> Trie -> Trie 
unitS pol i Nil = Nil
unitS pol i End = End 
unitS pol i tr@(Tr j p n r) | i == j = if pol 
                                       then nubT (Tr j Nil n r)
                                       else nubT (Tr j p Nil r) 
                            | i < j  = tr
                            | i > j  = nubT (Tr
                                        j
                                        (unitS pol i p)
                                        (unitS pol i n)
                                        (unitS pol i r)
                                       )

unitR ::  Bool -> Integer -> Trie -> Trie 
unitR pol i Nil = Nil 
unitR pol i End = End 
unitR pol i tr@(Tr j p n r) | i == j = if pol 
                                       then 
                                       nubT (Tr
                                        j
                                        p 
                                        Nil
                                        (trieMerge n r)
                                       )
                                       else
                                       nubT (Tr
                                        j
                                        Nil 
                                        n
                                        (trieMerge p r)
                                       )
                            | i < j  = tr
                            | i > j  = nubT (Tr
                                        j
                                        (unitR pol i p)
                                        (unitR pol i n)
                                        (unitR pol i r)
                                       )

setTrue :: Integer -> Trie -> Trie 
setTrue i Nil = Nil
setTrue i End = End
setTrue i tr@(Tr j p n r) | i == j = trieMerge n r
                          | i < j  = tr
                          | i > j  = (Tr
                                      j
                                      (setTrue i p)
                                      (setTrue i n)
                                      (setTrue i r)
                                     )

setFalse :: Integer -> Trie -> Trie 
setFalse i Nil = Nil
setFalse i End = End
setFalse i tr@(Tr j p n r) | i == j = trieMerge p r
                           | i < j  = tr
                           | i > j  = (Tr
                                      j
                                      (setFalse i p)
                                      (setFalse i n)
                                      (setFalse i r)
                                     )

split :: (Valuation,Trie) -> [(Valuation,Trie)]
split (v,Nil) = [(v,Nil)] 
split (v,End) = [] 
split (v, tr@(Tr i p n r)) = [(v++[i], setTrue i tr),
                              (v++[-i],setFalse i tr)]

dpll :: (Valuation,Trie) -> [(Valuation,Trie)]
dpll (val,Nil) = [(val,Nil)]
dpll (val,End) = []
dpll (val,tr) = 
  concat [ dpll vt | vt <- (split.unitProp) (val,tr) ]

dp :: ClauseSet -> [(Valuation,Trie)]
dp cls = dpll ([], (cls2trie . rSort) (clsNub cls))

