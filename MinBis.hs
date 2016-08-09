module MinBis where 

import Data.List
import Models 

lookupFs :: (Eq a,Eq b) => a -> a -> [(a,b)] -> (b -> b -> Bool) -> Bool
lookupFs i j table r = case lookup i table of 
  Nothing -> lookup j table == Nothing 
  Just f1 -> case lookup j table of 
      Nothing -> False 
      Just f2 -> r f1 f2

initPartition :: (Eq a, Eq b) => Model a b -> (b -> b -> Bool) -> [[a]]
initPartition (Mo states pre rel) r = 
  rel2part states (\ x y -> lookupFs x y pre r)

refinePartition :: (Eq a, Eq b) => Model a b -> [[a]] -> [[a]]
refinePartition m p = refineP m p p 
  where 
  refineP :: (Eq a, Eq b) => Model a b -> [[a]] -> [[a]] -> [[a]]
  refineP m part [] = []
  refineP m@(Mo states pre rel) part (block:blocks) = 
     newblocks ++ (refineP m part blocks) 
       where 
         newblocks = 
           rel2part block (\ x y -> sameAccBlocks m part x y) 

sameAccBlocks :: (Eq a, Eq b) => 
         Model a b -> [[a]] -> a -> a -> Bool
sameAccBlocks m@(Mo states pre rel) part s t = 
    and [ accBlocks m part s ag == accBlocks m part t  ag | 
                                               ag <- all_agents ]

accBlocks :: (Eq a, Eq b) => Model a b -> [[a]] -> a -> Agent -> [[a]]
accBlocks m@(Mo states pre rel) part s ag = 
    nub [ bl part y | (ag',x,y) <- rel, ag' == ag, x == s ]

bl :: (Eq a) => [[a]] -> a -> [a]
bl part x = head (filter (\ b -> elem x b) part)

initRefine :: (Eq a, Eq b) => Model a b -> (b -> b -> Bool) -> [[a]]
initRefine m r = refine m (initPartition m r)

refine :: (Eq a, Eq b) => Model a b -> [[a]] -> [[a]]
refine m part = if rpart == part 
                       then part 
                       else refine m rpart 
  where rpart = refinePartition m part 

minimalModel :: (Eq a, Ord a, Eq b, Ord b) => 
                 (b -> b -> Bool) -> Model a b -> Model [a] b
minimalModel r m@(Mo states pre rel) = 
  (Mo states' pre' rel') 
     where
     partition = initRefine m r
     states'   = partition 
     f         = bl partition
     rel'      = (nub.sort) (map (\ (x,y,z) -> (x, f y, f z)) rel)
     pre'      = (nub.sort) (map (\ (x,y)   -> (f x, y))      pre)

minimalPmod :: (Eq a, Ord a, Eq b, Ord b) => 
                  (b -> b -> Bool) -> Pmod a b -> Pmod [a] b
minimalPmod r (Pmod sts pre rel pts) = (Pmod sts' pre' rel' pts') 
  where (Mo sts' pre' rel') = minimalModel r (Mo sts pre rel)
        pts' = map (bl sts') pts

convert :: (Eq a, Show a) => [a] -> a  -> Integer
convert = convrt 0 
  where 
  convrt :: (Eq a, Show a) => Integer -> [a] -> a -> Integer 
  convrt n []     x = error (show x ++ " not in Data.List")
  convrt n (y:ys) x | x == y    = n
                    | otherwise = convrt (n+1) ys x 

conv ::  (Eq a, Show a) => Model a b -> Model Integer b
conv  (Mo worlds val acc) = 
      (Mo (map f worlds) 
          (map (\ (x,y)   -> (f x, y)) val)
          (map (\ (x,y,z) -> (x, f y, f z)) acc))
  where f = convert worlds

convPmod ::  (Eq a, Show a) => Pmod a b -> Pmod Integer b
convPmod (Pmod sts pre rel pts) = (Pmod sts' pre' rel' pts') 
   where (Mo sts' pre' rel') = conv (Mo sts pre rel)
         pts' = nub (map (convert sts) pts)

bisim ::  (Eq a, Ord a, Show a, Eq b, Ord b) => 
           (b -> b -> Bool) -> Model a b -> Model Integer b 
bisim r = conv . (minimalModel r)

bisimPmod ::  (Eq a, Ord a, Show a, Eq b, Ord b) => 
            (b -> b -> Bool) -> Pmod a b -> Pmod Integer b
bisimPmod r = convPmod . (minimalPmod r)

