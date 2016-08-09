module MinAE
where 

import Data.List
import Models
import MinBis
import ActEpist

unfold :: PoAM -> PoAM
unfold (Pmod states pre acc [])     = zero
unfold am@(Pmod states pre acc [p]) = am
unfold (Pmod states pre acc points) = 
  Pmod states' pre' acc' points'
  where 
  len = toInteger (length states)
  points' = [ p + len | p <- points ]
  states' = states ++ points' 
  pre'    = pre ++ [ (j+len,f) | (j,f) <- pre, k <- points, j == k ]
  acc'    = acc ++ [ (ag,i+len,j) | (ag,i,j) <- acc, k <- points, i == k ]

preds, sucs :: (Eq a, Ord a, Eq b, Ord b) => [(a,b,b)] -> b -> [(a,b)]
preds rel s = (sort.nub) [ (ag,s1) | (ag,s1,s2) <- rel, s == s2 ]
sucs  rel s = (sort.nub) [ (ag,s2) | (ag,s1,s2) <- rel, s == s1 ]

psPartition :: (Eq a, Ord a, Eq b) => Model a b -> [[a]]
psPartition (Mo states pre rel) = 
  rel2part states (\ x y -> preds rel x == preds rel y 
                            && 
                            sucs rel x == sucs rel y)

minPmod :: (Eq a, Ord a) => Pmod a Form -> Pmod [a] Form
minPmod pm@(Pmod states pre rel pts) = 
  (Pmod states' pre' rel' pts') 
     where
     m         = Mo states pre rel
     partition = refine m (psPartition m)
     states'   = partition 
     f         = bl partition
     g         = \ xs -> canonF (Disj (map (table2fct pre) xs))
     rel'      = (nub.sort) (map (\ (x,y,z) -> (x, f y, f z)) rel)
     pre'      = zip states' (map g states')
     pts'      = map (bl states') pts

aePmod ::  (Eq a, Ord a, Show a) => Pmod a Form -> Pmod State Form
--aePmod ::  PoAM -> PoAM
aePmod = (bisimPmod propEquiv) . minPmod . unfold . 
                          (bisimPmod propEquiv) . gsmPoAM . convPmod

