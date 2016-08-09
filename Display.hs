module Display 
where 

import Data.Char
import Data.List
import Models

accFor :: Eq a => a -> [(a,b,b)] -> [(b,b)]
accFor label triples = [ (x,y) | (label',x,y) <- triples, label == label' ]

containedIn :: Eq a => [a] -> [a] -> Bool
containedIn [] ys     = True
containedIn (x:xs) ys = elem x ys && containedIn xs ys

idR :: Eq a => [a] -> [(a,a)]
idR = map (\x -> (x,x))

reflR :: Eq a => [a] -> [(a,a)] -> Bool
reflR xs r = containedIn (idR xs) r 

symR :: Eq a => [(a,a)] -> Bool
symR [] = True 
symR ((x,y):pairs) | x == y    = symR (pairs)
                   | otherwise = elem (y,x) pairs 
                                 && symR (pairs \\ [(y,x)])

transR :: Eq a => [(a,a)] -> Bool
transR [] = True
transR s = and [ trans pair s | pair <- s ] 
   where 
   trans (x,y) r = and [ elem (x,v) r | (u,v) <- r, u == y ] 

equivalenceR :: Eq a => [a] -> [(a,a)] -> Bool 
equivalenceR xs r = reflR xs r && symR r && transR r 

isS5 :: (Eq a) => [a] -> [(Agent,a,a)] -> Bool
isS5 xs triples = 
  all (equivalenceR xs) rels
    where rels = [ accFor i triples | i <- all_agents ]

pairs2rel :: (Eq a, Eq b) => [(a,b)] -> a -> b -> Bool
pairs2rel pairs = \ x y -> elem (x,y) pairs

equiv2part :: Eq a => [a] -> [(a,a)] -> [[a]]
equiv2part xs r = rel2part xs (pairs2rel r)

euclideanR :: Eq a => [(a,a)] -> Bool
euclideanR s = and [ eucl pair s | pair <- s ] 
  where 
  eucl (x,y) r = and [ elem (y,v) r | (u,v) <- r, u == x ] 

serialR :: Eq a => [a] -> [(a,a)] -> Bool
serialR [] s = True
serialR (x:xs) s = any (\ p -> (fst p) == x) s && serialR xs s

kd45R :: Eq a => [a] -> [(a,a)] -> Bool
kd45R xs r = transR r && serialR xs r && euclideanR r

k45R :: Eq a => [(a,a)] -> Bool
k45R r = transR r && euclideanR r

isolated  :: Eq a =>  [(a,a)] -> a -> Bool
isolated r x = notElem x (map fst r ++ map snd r)

k45PointsBalloons :: Eq a => [a] -> [(a,a)] -> Maybe ([a],[([a],[a])])
k45PointsBalloons xs r = 
  let 
     orphans = filter (isolated r) xs
     ys = xs \\ orphans 
  in 
    case kd45Balloons ys r of 
      Just balloons -> Just (orphans,balloons) 
      Nothing       -> Nothing 

entryPair :: Eq a => [(a,a)] -> (a,a) -> Bool
entryPair r = \ (x,y) -> notElem (y,x) r

kd45Balloons :: Eq a => [a] -> [(a,a)] -> Maybe [([a],[a])]
kd45Balloons xs r = 
  let 
     (s,t)          = partition (entryPair r) r 
     entryPoints    = map fst s
     nonentryPoints = xs \\ entryPoints
     s5part xs r = if equivalenceR xs r 
                      then Just (equiv2part xs t)
                      else Nothing 
  in 
    case s5part nonentryPoints t of 
      Just part -> 
        Just [ (nub (map fst (filter (\ (x,y) -> elem y block) s)),
                block) |     block <- part                            ]
      Nothing   -> 
        Nothing

k45 :: (Eq a, Ord a) => [a] -> 
    [(Agent,a,a)] -> Maybe [(Agent,([a],[([a],[a])]))]
k45 xs triples = 
  if and [ maybe False (\ x -> True) b | (a,b) <- results  ] 
     then Just [ (a, maybe undefined id b) | (a,b) <- results  ] 
     else Nothing 
       where rels     = [ (a, accFor a triples)  | a     <- all_agents ]
             results  = [ (a, k45PointsBalloons xs r) | (a,r) <- rels   ]

kd45 :: (Eq a, Ord a) => [a] -> [(Agent,a,a)] -> Maybe [(Agent,[([a],[a])])]
kd45 xs triples = 
  if and [ maybe False (\ x -> True) b | (a,b) <- balloons ] 
     then Just [ (a, maybe undefined id b) | (a,b) <- balloons ] 
     else Nothing 
       where rels     = [ (a, accFor a triples)  | a     <- all_agents ]
             balloons = [ (a, kd45Balloons xs r) | (a,r) <- rels       ]

kd45psbs2balloons :: (Eq a, Ord a) => 
  [(Agent,([a],[([a],[a])]))] -> Maybe [(Agent,[([a],[a])])]
kd45psbs2balloons psbs = 
  if all (\ x -> x == []) entryList
     then Just balloons 
     else Nothing 
  where 
    entryList  = [ fst bs      | (a,bs) <- psbs ]
    balloons   = [ (a, snd bs) | (a,bs) <- psbs ]  

s5ball2part :: (Eq a, Ord a) => 
  [(Agent,[([a],[a])])] -> Maybe [(Agent,[[a]])]
s5ball2part balloons = 
  if all (\ x -> x == []) entryList 
     then Just partitions 
     else Nothing 
  where 
    entryList  = [ concat (map fst bs) | (a,bs) <- balloons ]
    partitions = [ (a, map snd bs)     | (a,bs) <- balloons ]  

display :: Show a => Int -> [a] -> IO()
display n = if n < 1 then error "parameter not positive"
                     else display' n n
  where 
  display' ::  Show a => Int -> Int -> [a] -> IO()
  display' n m [] = putChar '\n' 
  display' n 1 (x:xs) =   do (putStr . show) x
                             putChar '\n'
                             display' n n xs 
  display' n m (x:xs) =   do (putStr . show) x
                             display' n (m-1) xs 

showMo :: (Eq state, Show state, Ord state, Show formula) => 
                Model state formula -> IO()
showMo = displayM 10

showM :: (Eq state, Show state, Ord state, Show formula) => 
                               Pmod state formula -> IO()
showM (Pmod sts pre acc pnts) = do putStr "==> " 
                                   print pnts
                                   showMo (Mo sts pre acc)

showMs :: (Eq state, Show state, Ord state, Show formula) => 
                               [Pmod state formula] -> IO()
showMs ms = sequence_ (map showM ms)

displayM :: (Eq state, Show state, Ord state, Show formula) => 
                Int -> Model state formula -> IO()
displayM n (Mo states pre rel) = 
  do print states
     display (div n 2) pre 
     case (k45 states rel) of 
       Nothing       -> display n rel
       Just psbs     -> case kd45psbs2balloons psbs of 
         Nothing       -> displayPB (div n 2) psbs
         Just balloons -> case s5ball2part balloons of 
           Nothing          ->  displayB (div n 2) balloons
           Just parts       ->  displayP (2*n) parts 

displayP :: Show a => Int -> [(Agent,[[a]])] -> IO()
displayP n parts = sequence_ (map (display n) (map (\x -> [x]) parts))

displayB :: Show a => Int -> [(Agent,[([a],[a])])] -> IO()
displayB n balloons = sequence_ (map (display n) (map (\x -> [x]) balloons))

displayPB :: Show a => Int ->  [(Agent,([a],[([a],[a])]))] -> IO()
displayPB n  psbs = sequence_ (map (display n) (map (\x -> [x]) psbs))

class Show a => GraphViz a where 
  graphviz :: a -> String

glueWith :: String -> [String] -> String
glueWith _ []     = []
glueWith _ [y]    = y
glueWith s (y:ys) = y ++ s ++ glueWith s ys

listState  :: (Show a, Show b, Eq a, Eq b) => a -> [(a,b)] -> String
listState w val =
    let 
      props = head (maybe [] (\ x -> [x]) (lookup w val))
      label = filter (isAlphaNum) (show props)
    in 
      if null label 
         then show w 
         else show w 
              ++ "[label =\"" ++ (show w) ++ ":" ++ (show props) ++ "\"]"

links :: (Eq a, Eq b) => [(a,b,b)] -> [(a,b,b)]
links [] = []
links ((x,y,z):xyzs) | y == z    = links xyzs
                     | otherwise = 
                       (x,y,z): links (filter (/= (x,z,y)) xyzs)

cmpl :: Eq b => [(Agent,b,b)] -> [([Agent],b,b)]
cmpl [] = []
cmpl ((x,y,z):xyzs) = (xs,y,z):(cmpl xyzs') 
  where xs = x: [ a | a  <- all_agents, elem a (map f xyzs1) ]
        xyzs1 = filter (\ (u,v,w) -> 
                       (v == y && w == z) 
                               ||  
                       (v == z && w == y)) xyzs
        f (x,_,_) = x
        xyzs' = xyzs \\ xyzs1

instance (Show a, Show b, Eq a, Eq b) => GraphViz (Model a b) where 
  graphviz (Mo states val rel) = if isS5 states rel 
   then
    "digraph G { " 
      ++
      glueWith  " ; " [ listState s val | s <- states ]
      ++  " ; " ++
      glueWith " ; " [ (show s) ++ " -> " ++ (show s') 
                                ++ " [label=" 
                                ++ (filter isAlpha (show ags)) 
                                ++ ",dir=none ]"  |
                         s <- states, s' <- states, 
                         (ags,t,t') <- (cmpl . links) rel, 
                         s == t, s' == t'                         ]
      ++ " }"
   else
    "digraph G { " 
      ++
      glueWith  " ; " [ listState s val | s <- states ]
      ++  " ; " ++
      glueWith " ; " [ (show s) ++ " -> " ++ (show s') 
                                ++ " [label=" ++ (show ag) ++ "]"  |
                         s <- states, s' <- states, 
                         (ag,t,t') <- rel, 
                         s == t, s' == t'                         ]
      ++ " }"

listPState  :: (Show a, Show b, Eq a, Eq b) => 
                a -> [(a,b)] -> Bool -> String
listPState w val pointed =
    let 
      props = head (maybe [] (\ x -> [x]) (lookup w val))
      label = filter (isAlphaNum) (show props)
    in 
      if null label 
         then if pointed then show w ++ "[peripheries = 2]"
              else            show w 
         else if pointed then 
              show w 
              ++ "[label =\"" ++ (show w) ++ ":" ++ (show props) ++ 
                 "\",peripheries = 2]"
              else show w 
              ++ "[label =\"" ++ (show w) ++ ":" ++ (show props) ++ "\"]"

instance (Show a, Show b, Eq a, Eq b) => GraphViz (Pmod a b)  where 
  graphviz (Pmod states val rel points) = if isS5 states rel 
   then
    "digraph G { " 
      ++
      glueWith  " ; " [ listPState s val (elem s points) | s <- states ]
      ++  " ; " ++
      glueWith " ; " [ (show s) ++ " -> " ++ (show s') 
                                ++ " [label=" 
                                ++ (filter isAlpha (show ags)) 
                                ++  ",dir=none ]"  |
                         s <- states, s' <- states, 
                         (ags,t,t') <- (cmpl . links) rel, 
                         s == t, s' == t'                         ]
      ++ " }"
   else
    "digraph G { " 
      ++
      glueWith  " ; " [ listPState s val (elem s points) | s <- states ]
      ++  " ; " ++ 
      glueWith " ; " [ (show s) ++ " -> " ++ (show s') 
                                ++ " [label=" ++ (show ag) ++ "]"  |
                         s <- states, s' <- states, 
                         (ag,t,t') <- rel, 
                         s == t, s' == t'                         ]
      ++ " }"

writeGraph :: String -> IO()
writeGraph cts = writeFile "graph.dot" cts

writeGr :: String -> String -> IO()
writeGr name cts = writeFile name cts

writeModel :: (Show a, Show b, Eq a, Eq b) => Model a b -> IO()
writeModel m = writeGraph (graphviz m) 

writePmod :: (Show a, Show b, Eq a, Eq b) => (Pmod a b) -> IO()
writePmod m = writeGraph (graphviz m) 

writeP :: (Show a, Show b, Eq a, Eq b) => String -> (Pmod a b) -> IO()
writeP name m = writeGr (name ++ ".dot") (graphviz m) 

