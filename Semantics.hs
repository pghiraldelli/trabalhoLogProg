module Semantics
where 

import Data.List
import Data.Char
import Models
import Display
import MinBis
import ActEpist
import MinAE
import DPLL 

groupAlts :: [(Agent,State,State)] -> [Agent] -> State -> [State]
groupAlts rel agents current = 
  (nub . sort . concat) [ alternatives rel a current | a <- agents ]

commonAlts :: [(Agent,State,State)] -> [Agent] -> State -> [State]
commonAlts rel agents current = 
  closure rel agents (groupAlts rel agents current) 

up :: EpistM -> PoAM -> Pmod (State,State) [Prop]
up  m@(Pmod worlds val acc points) am@(Pmod states pre susp actuals) = 
   Pmod worlds' val' acc' points'
   where 
   worlds' = [ (w,s) | w <- worlds, s <- states, 
                       formula <- maybe [] (\ x -> [x]) (lookup s pre), 
                       isTrAt w m formula                ]
   val'    = [ ((w,s),props) | (w,props) <- val, 
                                s        <- states, 
                                elem (w,s) worlds'             ]
   acc'    = [ (ag1,(w1,s1),(w2,s2)) | (ag1,w1,w2) <- acc, 
                                       (ag2,s1,s2) <- susp, 
                                        ag1 == ag2, 
                                        elem (w1,s1) worlds', 
                                        elem (w2,s2) worlds'   ]
   points' = [ (p,a) | p <- points, a <- actuals, 
                       elem (p,a) worlds'                      ]

sameVal :: [Prop] -> [Prop] -> Bool
sameVal ps qs = (nub . sort) ps ==  (nub . sort) qs

upd ::  EpistM -> PoAM -> EpistM
upd sm am = (bisimPmod (sameVal) . convPmod) (up sm am)

upds  :: EpistM -> [PoAM] -> EpistM
upds = foldl upd 

reachableAut :: SM -> NFA State -> State -> [State]
reachableAut model nfa@(NFA start moves final) w = 
  acc model nfa [(w,start)] []
  where 
    acc :: SM -> NFA State -> [(State,State)] -> [(State,State)] -> [State]
    acc model (NFA start moves final) [] marked =  
       (sort.nub) (map fst (filter (\ x -> snd x == final) marked))
    acc m@(Mo states _ rel) nfa@(NFA start moves final) 
          ((w,s):pairs) marked = 
      acc m nfa (pairs ++ (cs \\ pairs)) (marked ++ cs)
      where 
        cs = nub ([ (w, s') | Move t (Tst f) s' <- moves, 
                              t == s, notElem (w,s') marked, 
                              isTrueAt w m f ]
                  ++
                 [ (w',s') | Move t (Acc ag) s' <- moves, t == s, 
                             w' <- states, 
                             notElem (w',s') marked, 
                             elem (ag,w,w') rel ])

isTrueAt :: State -> SM -> Form -> Bool
isTrueAt w m Top = True 
isTrueAt w m@(Mo worlds val acc) (Prop p) = 
  elem p (concat [ props | (w',props) <- val, w'==w ])
isTrueAt w m (Neg f)   = not (isTrueAt w m f) 
isTrueAt w m (Conj fs) = and (map (isTrueAt w m) fs)
isTrueAt w m (Disj fs) = or  (map (isTrueAt w m) fs)

isTrueAt w m@(Mo worlds val acc) (K ag f) = 
  and (map (flip ((flip isTrueAt) m) f) (alternatives acc ag w))
isTrueAt w m@(Mo worlds val acc) (EK agents f) = 
  and (map (flip ((flip isTrueAt) m) f) (groupAlts acc agents w))
isTrueAt w m@(Mo worlds val acc) (CK agents f) = 
  and (map (flip ((flip isTrueAt) m) f) (commonAlts acc agents w))

isTrueAt w m (Up am f) = 
  and [ isTrueAt w' m' f | 
         (m',w') <- decompose (upd (mod2pmod m [w]) am) ]
isTrueAt w m (Aut nfa f) = 
  and [ isTrueAt w' m f | w' <- reachableAut m nfa w ]

isTrAt :: State -> EpistM -> Form -> Bool
isTrAt w (Pmod worlds val rel pts) = isTrueAt w (Mo worlds val rel)

isTrue :: EpistM -> Form -> Bool
isTrue (Pmod worlds val rel pts) form = 
   and [ isTrueAt w (Mo worlds val rel) form | w <- pts ]

initE :: [Prop] -> EpistM 
initE allProps = (Pmod worlds val accs points)
  where 
    worlds = [0..(2^k - 1)]
    k      = length allProps
    val    = zip worlds (sortL (powerList allProps))
    accs   = [ (ag,st1,st2) | ag <- all_agents, 
                              st1 <- worlds, 
                              st2 <- worlds      ]
    points = worlds

powerList  :: [a] -> [[a]]
powerList  [] = [[]]
powerList  (x:xs) = (powerList xs) ++ (map (x:) (powerList xs))

sortL :: Ord a => [[a]] -> [[a]]
sortL  = sortBy (\ xs ys -> if length xs < length ys then LT
                               else if length xs > length ys then GT
                               else compare xs ys) 

e00 :: EpistM
e00 = initE [P 0]

e0 :: EpistM
e0 = initE [P 0,Q 0] 

public :: Form -> PoAM
public form = 
   (Pmod [0] [(0,form)] [ (a,0,0) | a <- all_agents ] [0])

groupM :: [Agent] -> Form -> PoAM
groupM agents form = 
  if (sort agents) == all_agents 
    then public form 
    else 
      (Pmod 
         [0,1] 
         [(0,form),(1,Top)] 
         ([ (a,0,0) | a <- all_agents ] 
           ++ [ (a,0,1) | a <- all_agents \\ agents ] 
           ++ [ (a,1,0) | a <- all_agents \\ agents ] 
           ++ [ (a,1,1) | a <- all_agents           ])
         [0])

message :: Agent -> Form -> PoAM
message agent form = groupM [agent] form 

secret :: [Agent] -> Form -> PoAM
secret agents form = 
  if (sort agents) == all_agents 
    then public form 
    else 
      (Pmod 
         [0,1] 
         [(0,form),(1,Top)] 
         ([ (a,0,0) | a <- agents ] 
           ++ [ (a,0,1) | a <- all_agents \\ agents ] 
           ++ [ (a,1,1) | a <- all_agents           ])
         [0])

test :: Form -> PoAM
test = secret [] 

reveal :: [Agent] -> [Form] -> PoAM
reveal ags forms = 
  (Pmod 
     states
     (zip states forms)
     ([ (ag,s,s) | s <- states, ag <- ags ]
       ++
      [ (ag,s,s') | s <- states, s' <- states, ag <- others ])
     states)
    where states = map fst (zip [0..] forms)
          others = all_agents \\ ags

info :: [Agent] -> Form -> PoAM
info agents form = reveal agents [form, negation form]

one :: PoAM
one = public Top

cmpP :: PoAM -> PoAM ->
                 Pmod (State,State) Form
cmpP m@(Pmod states pre susp ss) (Pmod states' pre' susp' ss') = 
  (Pmod nstates npre nsusp npoints)
       where  
         npoints = [ (s,s') | s <- ss, s' <- ss' ]
         nstates = [ (s,s') | s <- states, s' <- states' ] 
         npre    = [ ((s,s'), g) | (s,f)     <- pre, 
                                   (s',f')   <- pre', 
                                    g        <- [computePre m f f']      ]
         nsusp   = [ (ag,(s1,s1'),(s2,s2')) | (ag,s1,s2)    <- susp, 
                                              (ag',s1',s2') <- susp', 
                                               ag == ag'                 ] 

computePre  :: PoAM -> Form -> Form -> Form
computePre m g g'  | pureProp conj = conj 
                   | otherwise     = Conj [ g, Neg (Up m (Neg g')) ] 
  where conj    = canonF (Conj [g,g'])

cmpPoAM :: PoAM -> PoAM -> PoAM
cmpPoAM pm pm' = aePmod (cmpP pm pm')

cmp :: [PoAM] -> PoAM
cmp = foldl cmpPoAM one

m2  = initE [P 0,Q 0]
psi = Disj[Neg(K b p),q]

pow :: Int -> PoAM -> PoAM
pow n am = cmp (take n (repeat am)) 

vBtest :: EpistM -> PoAM -> [EpistM]
vBtest m a = map (upd m) (star one cmpPoAM a)

star :: a -> (a -> a -> a) -> a -> [a]
star z f a = z : star (f z a) f a

vBfix :: EpistM -> PoAM -> [EpistM]
vBfix m a = fix (vBtest m a)

fix :: Eq a => [a] -> [a]
fix (x:y:zs) = if x == y then [x]
                         else x: fix (y:zs) 

m1  = initE [P 1,P 2,P 3] 
phi = Conj[p1,Neg (Conj[K a p1,Neg p2]), 
              Neg (Conj[K a p2,Neg p3])]
a1  = message a phi

ndSum' :: PoAM -> PoAM -> PoAM
ndSum' m1 m2 = (Pmod states val acc ss)
  where 
       (Pmod states1 val1 acc1 ss1) = convPmod m1
       (Pmod states2 val2 acc2 ss2) = convPmod m2
       f   = \ x -> toInteger (length states1) + x 
       states2' = map f states2
       val2'    = map (\ (x,y)   -> (f x, y)) val2
       acc2'    = map (\ (x,y,z) -> (x, f y, f z)) acc2
       ss       = ss1 ++ map f ss2
       states   = states1 ++ states2'
       val      = val1 ++ val2' 
       acc      = acc1 ++ acc2' 

am0 = ndSum' (test p) (test (Neg p))

am1 = ndSum' (test p) (ndSum' (test q) (test r))

ndSum :: PoAM -> PoAM -> PoAM
ndSum m1 m2 = aePmod (ndSum' m1 m2)

ndS :: [PoAM] -> PoAM
ndS = foldl ndSum zero

testAnnounce :: Form -> PoAM
testAnnounce form = ndS [ cmp [ test form, public form ], 
                          cmp [ test (negation form), 
                                public (negation form)] ]

