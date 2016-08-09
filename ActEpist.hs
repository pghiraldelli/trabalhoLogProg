{-# LANGUAGE DatatypeContexts #-}

module ActEpist 
where 

import Data.List
import Models
import MinBis
import DPLL

data Prop = P Int | Q Int | R Int | S Int deriving (Eq,Ord) 

instance Show Prop where 
  show (P 0) = "p"; show (P i) = "p" ++ show i 
  show (Q 0) = "q"; show (Q i) = "q" ++ show i 
  show (R 0) = "r"; show (R i) = "r" ++ show i
  show (S 0) = "s"; show (S i) = "s" ++ show i

data Form = Top 
          | Prop Prop 
          | Neg  Form 
          | Conj [Form]
          | Disj [Form]
          | Pr Program Form
          | K Agent Form 
          | EK [Agent] Form
          | CK [Agent] Form
          | Up PoAM Form 
          | Aut (NFA State) Form
          deriving (Eq,Ord)

data Program = Ag Agent 
             | Ags [Agent]
             | Test Form 
             | Conc [Program]
             | Sum  [Program]
             | Star Program 
             deriving (Eq,Ord)

impl :: Form -> Form -> Form 
impl form1 form2 = Disj [Neg form1, form2]

equiv :: Form -> Form -> Form 
equiv form1 form2 = Conj [form1 `impl` form2, form2 `impl` form1]

negation :: Form -> Form
negation (Neg form) = form
negation form       = Neg form

instance Show Form where 
  show Top = "T" ; show (Prop p) = show p; show (Neg f) = '-':(show f); 
  show (Conj fs)     = '&': show fs
  show (Disj fs)     = 'v': show fs
  show (Pr p f)      = '[': show p ++ "]" ++ show f 
  show (K agent f)   = '[': show agent ++ "]" ++ show f 
  show (EK agents f) = 'E': show agents ++ show f
  show (CK agents f) = 'C': show agents ++ show f
  show (Up pam f)    = 'A': show (points pam) ++ show f 
  show (Aut aut f)   = '[': show aut ++ "]" ++ show f 

instance Show Program where 
  show (Ag a)       = show a 
  show (Ags as)     = show as
  show (Test f)     = '?': show f
  show (Conc ps)    = 'C': show ps 
  show (Sum ps)     = 'U': show ps
  show (Star p)     = '(': show p ++ ")*" 

splitU :: [Program] -> ([Form],[Agent],[Program])
splitU [] = ([],[],[])
splitU (Test f: ps) = (f:fs,ags,prs) 
  where (fs,ags,prs) = splitU ps
splitU (Ag x: ps) = (fs,union [x] ags,prs) 
  where (fs,ags,prs) = splitU ps
splitU (Ags xs: ps) = (fs,union xs ags,prs) 
  where (fs,ags,prs) = splitU ps
splitU (Sum ps: ps') = splitU (union ps ps') 
splitU (p:ps)        = (fs,ags,p:prs) 
  where (fs,ags,prs) = splitU ps

comprC :: [Program] -> [Program]
comprC [] = []
comprC (Test Top: ps)          = comprC ps
comprC (Test (Neg Top): ps)    = [Test (Neg Top)]
comprC (Test f: Test f': rest) = comprC (Test (canonF (Conj [f,f'])): rest)
comprC (Conc ps : ps')         = comprC (ps ++ ps') 
comprC (p:ps)                  = let ps' = comprC ps 
                                 in 
                                   if ps' == [Test (Neg Top)] 
                                     then [Test (Neg Top)]
                                     else p: ps'

simpl :: Program -> Program 
simpl (Ag x)                    = Ag x
simpl (Ags [])                  = Test (Neg Top)
simpl (Ags [x])                 = Ag x
simpl (Ags xs)                  = Ags xs
simpl (Test f)                  = Test (canonF f)

simpl (Sum prs) = 
  let (fs,xs,rest) = splitU (map simpl prs)
      f            = canonF (Disj fs) 
  in 
    if xs == [] && rest == []                            
      then Test f
    else if xs == [] && f == Neg Top && length rest == 1 
      then (head rest)
    else if xs == [] && f == Neg Top 
      then Sum rest
    else if xs == []
      then Sum (Test f: rest)
    else if length xs == 1  && f == Neg Top              
      then Sum (Ag (head xs): rest)
    else if length xs == 1 
      then Sum (Test f: Ag (head xs): rest) 
    else if f == Neg Top
      then Sum (Ags xs: rest)  
    else Sum (Test f: Ags xs: rest)  

simpl (Conc prs) = 
    let prs' = comprC (map simpl prs)
    in 
      if prs'== []                  then Test Top
      else if length prs' == 1      then head prs'
      else if head prs' == Test Top then Conc (tail prs')
      else                               Conc prs'

simpl (Star pr) = case simpl pr of 
    Test f             -> Test Top
    Sum [Test f, pr']  -> Star pr'
    Sum (Test f: prs') -> Star (Sum prs') 
    Star pr'           -> Star pr'
    pr'                -> Star pr'

pureProp ::  Form -> Bool
pureProp Top       = True
pureProp (Prop _)  = True 
pureProp (Neg f)   = pureProp f 
pureProp (Conj fs) = and (map pureProp fs)
pureProp (Disj fs) = and (map pureProp fs)
pureProp  _        = False 

bot, p0, p, p1, p2, p3, p4, p5, p6 :: Form 
bot = Neg Top 
p0 = Prop (P 0); p = p0; p1  = Prop (P 1); p2 = Prop (P 2)
p3 = Prop (P 3); p4 = Prop (P 4); p5 = Prop (P 5); p6 = Prop (P 6)

q0, q, q1, q2, q3, q4, q5, q6 :: Form 
q0 = Prop (Q 0); q = q0; q1  = Prop (Q 1); q2 = Prop (Q 2); 
q3 = Prop (Q 3); q4 = Prop (Q 4); q5 = Prop (Q 5); q6 = Prop (Q 6)

r0, r, r1, r2, r3, r4, r5, r6:: Form 
r0 = Prop (R 0); r = r0; r1  = Prop (R 1); r2 = Prop (R 2)
r3 = Prop (R 3); r4 = Prop (R 4); r5 = Prop (R 5); r6 = Prop (R 6)

s0, s, s1, s2, s3, s4, s5, s6:: Form 
s0 = Prop (S 0); s = s0; s1  = Prop (S 1); s2 = Prop (S 2)
s3 = Prop (S 3); s4 = Prop (S 4); s5 = Prop (S 5); s6 = Prop (S 6)

u   = Up ::  PoAM -> Form -> Form

nkap = Neg (K a p)
nkanp = Neg (K a (Neg p))
nka_p = Conj [nkap,nkanp]

mapping :: Form -> [(Form,Integer)]
mapping f = zip lits [1..k]
  where 
  lits = (sort . nub . collect) f
  k    = toInteger (length lits)
  collect :: Form -> [Form]
  collect Top         = []
  collect (Prop p)    = [Prop p]
  collect (Neg f)     = collect f
  collect (Conj fs)   = concat (map collect fs)
  collect (Disj fs)   = concat (map collect fs)
  collect (Pr pr f)   = if canonF f == Top then [] else [Pr pr (canonF f)]
  collect (K ag f)    = if canonF f == Top then [] else [K ag (canonF f)]
  collect (EK ags f)  = if canonF f == Top then [] else [EK ags (canonF f)]
  collect (CK ags f)  = if canonF f == Top then [] else [CK ags (canonF f)]
  collect (Up pam f)  = if canonF f == Top then [] else [Up pam (canonF f)]
  collect (Aut nfa f) = if nfa == nullAut || canonF f == Top 
                        then [] else [Aut nfa (canonF f)]

cf :: (Form -> Integer) -> Form -> [[Integer]]
cf g (Top)            = []
cf g (Prop p)         = [[g (Prop p)]]
cf g (Pr pr f)        = if canonF f == Top then [] 
                        else [[g (Pr pr (canonF f))]]
cf g (K ag f)         = if canonF f == Top then [] 
                        else [[g (K ag (canonF f))]]
cf g (EK ags f)       = if canonF f == Top then [] 
                        else [[g (EK ags (canonF f))]]
cf g (CK ags f)       = if canonF f == Top then [] 
                        else [[g (CK ags (canonF f))]]
cf g (Up am f)        = if canonF f == Top then [] 
                        else [[g (Up am (canonF f))]]
cf g (Aut nfa f)      = if nfa == nullAut || canonF f == Top then [] 
                        else [[g (Aut nfa (canonF f))]]
cf g (Conj fs)        = concat (map (cf g) fs) 
cf g (Disj fs)        = deMorgan (map (cf g) fs)

cf g (Neg Top)        = [[]]
cf g (Neg (Prop p))   = [[- g (Prop p)]]
cf g (Neg (Pr pr f))  = if canonF f == Top then [[]] 
                        else [[- g (Pr pr (canonF f))]]
cf g (Neg (K ag f))   = if canonF f == Top then [[]] 
                        else [[- g (K ag (canonF f))]]
cf g (Neg (EK ags f)) = if canonF f == Top then [[]] 
                        else [[- g (EK ags (canonF f))]]
cf g (Neg (CK ags f)) = if canonF f == Top then [[]] 
                        else [[- g (CK ags (canonF f))]]
cf g (Neg (Up am f))  = if canonF f == Top then [[]] 
                        else [[- g (Up am (canonF f))]]
cf g (Neg (Aut nfa f))= if nfa == nullAut || canonF f == Top then [[]] 
                        else [[- g (Aut nfa (canonF f))]]
cf g (Neg (Conj fs))  = deMorgan (map (\ f -> cf g (Neg f)) fs)
cf g (Neg (Disj fs))  = concat   (map (\ f -> cf g (Neg f)) fs)
cf g (Neg (Neg f))    = cf g f 

deMorgan :: [[[Integer]]] -> [[Integer]]
deMorgan [] = [[]]
deMorgan [cls] = cls
deMorgan (cls:clss) = deMorg cls (deMorgan clss) 
  where 
  deMorg :: [[Integer]] -> [[Integer]] -> [[Integer]]
  deMorg cls1 cls2 = (nub . concat) [ deM cl cls2 | cl <- cls1 ]  
  deM :: [Integer] -> [[Integer]]  -> [[Integer]]
  deM cl cls = map (fuseLists cl) cls 

fuseLists :: [Integer] -> [Integer] -> [Integer]
fuseLists [] ys = ys
fuseLists xs [] = xs
fuseLists (x:xs) (y:ys) | abs x < abs y  = x:(fuseLists xs (y:ys))
                        | abs x == abs y = if x == y 
                                              then x:(fuseLists xs ys) 
                                              else if x > y 
                                                then x:y:(fuseLists xs ys)
                                                else y:x:(fuseLists xs ys)
                        | abs x > abs y  = y:(fuseLists (x:xs) ys)

satVals :: [(Form,Integer)] -> Form -> [[Integer]]
satVals t f = (map fst . dp) (cf (table2fct t) f)

propEquiv :: Form -> Form -> Bool
propEquiv f1 f2 = satVals g f1 == satVals g f2
  where g = mapping (Conj [f1,f2])

contrad :: Form -> Bool
contrad f = propEquiv f (Disj [])

consistent :: Form -> Bool
consistent = not . contrad 

canonF :: Form -> Form 
canonF f = if (contrad (Neg f)) 
             then Top
             else if fs == []
             then Neg Top 
             else if length fs == 1 
             then head fs 
             else Disj fs
  where g   = mapping f 
        nss = satVals g f
        g'  = \ i -> head [ form | (form,j) <- g, i == j ]
        h   = \ i -> if i < 0 then Neg (g' (abs i)) else g' i 
        h'  = \ xs -> map h xs
        k   = \ xs -> if xs == [] 
                         then Top 
                         else if length xs == 1 
                                 then head xs 
                                 else Conj xs
        fs  = map k (map h' nss)

type State = Integer

type SM = Model State [Prop]

type EpistM = Pmod State [Prop]

valuation  :: EpistM -> [(State,[Prop])]
valuation pmod = eval $ fst (pmod2mp pmod)

type AM = Model State Form

type PoAM = Pmod State Form

preconditions :: PoAM -> [Form]
preconditions (Pmod states pre acc points) = 
   map (table2fct pre) points 

precondition :: PoAM -> Form
precondition am = canonF (Conj (preconditions am))

zero :: PoAM 
zero = Pmod [] [] [] [] 

gsmPoAM :: PoAM -> PoAM 
gsmPoAM (Pmod states pre acc points) = 
  let 
    points' = [ p | p <- points, consistent (table2fct pre p) ]
    states' = [ s | s <- states, consistent (table2fct pre s) ]
    pre'    = filter (\ (x,_) -> elem x states') pre
    f       = \ (_,s,t) -> elem s states' && elem t states'
    acc'    = filter f acc 
  in 
  if points' == [] 
     then zero 
     else gsm (Pmod states' pre' acc' points')

transf :: PoAM -> Integer -> Integer -> Program -> Program 
transf am@(Pmod states pre acc points) i j (Ag ag) = 
   let 
     f = table2fct pre i
   in 
   if elem (ag,i,j) acc && f == Top          then Ag ag
   else if elem (ag,i,j) acc && f /= Neg Top then Conc [Test f, Ag ag]
   else Test (Neg Top) 
transf am@(Pmod states pre acc points) i j (Ags ags) = 
   let ags' = nub [ a | (a,k,m) <- acc, elem a ags, k == i, m == j ]
       ags1 = intersect ags ags'
       f    = table2fct pre i
   in 
     if ags1 == [] || f == Neg Top        then Test (Neg Top) 
     else if f == Top && length ags1 == 1 then Ag (head ags1) 
     else if f == Top                     then Ags ags1
     else Conc [Test f, Ags ags1]
transf am@(Pmod states pre acc points) i j (Test f) = 
   let 
     g = table2fct pre i 
   in 
   if i == j 
      then Test (Conj [g,(Up am f)])
      else Test (Neg Top)
transf am@(Pmod states pre acc points) i j (Conc [])  = 
  transf am i j (Test Top) 
transf am@(Pmod states pre acc points) i j (Conc [p]) = transf am i j p
transf am@(Pmod states pre acc points) i j (Conc (p:ps)) = 
  Sum [ Conc [transf am i k p, transf am k j (Conc ps)] | k <- [0..n] ]
    where n = toInteger (length states - 1)
transf am@(Pmod states pre acc points) i j (Sum [])  = 
  transf am i j (Test (Neg Top))
transf am@(Pmod states pre acc points) i j (Sum [p]) = transf am i j p 
transf am@(Pmod states pre acc points) i j (Sum ps)  = 
  Sum [ transf am i j p | p <- ps ]
transf am@(Pmod states pre acc points) i j (Star p) = kleene am i j n p
  where n = toInteger (length states)

kleene ::  PoAM -> Integer -> Integer -> Integer -> Program -> Program 
kleene am i j 0 pr = 
  if i == j 
    then Sum [Test Top, transf am i j pr] 
    else transf am i j pr
kleene am i j k pr 
  | i == j && j == pred k = Star (kleene am i i i pr)
  | i == pred k           = 
    Conc [Star (kleene am i i i pr), kleene am i j i pr]
  | j == pred k           = 
    Conc [kleene am i j j pr, Star (kleene am j j j pr)]
  | otherwise             = 
      Sum [kleene am i j k' pr, 
           Conc [kleene am i k' k' pr, 
                 Star (kleene am k' k' k' pr), kleene am k' j k' pr]]
      where k' = pred k

tfm ::  PoAM -> Integer -> Integer -> Program -> Program 
tfm am i j pr = simpl (transf am i j pr)

step0, step1 :: PoAM -> Program -> Form -> Form
step0 am@(Pmod states pre acc []) pr f = Top 
step0 am@(Pmod states pre acc [i]) pr f = step1 am pr f
step0 am@(Pmod states pre acc is) pr f = 
  Conj [ step1 (Pmod states pre acc [i]) pr f | i <- is ]
step1 am@(Pmod states pre acc [i]) pr f = 
   Conj [ Pr (transf am i j (rpr pr)) 
              (Up (Pmod states pre acc [j]) f) | j <- states ] 

step :: PoAM -> Program -> Form -> Form
step am pr f = canonF (step0 am pr f)

t :: Form -> Form 
t Top = Top
t (Prop p) = Prop p 
t (Neg f) = Neg (t f)
t (Conj fs) = Conj (map t fs) 
t (Disj fs) = Disj (map t fs) 
t (Pr pr f) = Pr (rpr pr) (t f)
t (K x f)   = Pr (Ag x) (t f) 
t (EK xs f)  = Pr (Ags xs) (t f) 
t (CK xs f)  = Pr (Star (Ags xs)) (t f)

t (Up am@(Pmod states pre acc [i]) f) = t' am f
t (Up am@(Pmod states pre acc is) f)  = 
   Conj [ t' (Pmod states pre acc [i]) f | i <- is ]

t' :: PoAM -> Form -> Form
t' am Top            = Top
t' am (Prop p)       = impl (precondition am) (Prop p)
t' am (Neg f)        =  Neg (t' am f)
t' am (Conj fs)      = Conj (map (t' am) fs) 
t' am (Disj fs)      = Disj (map (t' am) fs)
t' am (K x f)        = t' am (Pr (Ag x) f)
t' am (EK xs f)      = t' am (Pr (Ags xs) f)
t' am (CK xs f)      = t' am (Pr (Star (Ags xs)) f)
t' am (Up am' f)     = t' am (t (Up am' f))

t' am@(Pmod states pre acc [i]) (Pr pr f) = 
   Conj [ Pr (transf am i j (rpr pr)) 
              (t' (Pmod states pre acc [j]) f) | j <- states ]
t' am@(Pmod states pre acc is) (Pr pr f) = 
   error "action model not single pointed"

rpr :: Program -> Program
rpr (Ag x)       = Ag x
rpr (Ags xs)     = Ags xs
rpr (Test f)     = Test (t f)
rpr (Conc ps)    = Conc (map rpr ps)
rpr (Sum  ps)    = Sum  (map rpr ps)
rpr (Star p)     = Star (rpr p) 

tr :: Form -> Form
tr = canonF . t

data Symbol = Acc Agent | Tst Form deriving (Eq,Ord,Show)

data (Eq a,Ord a,Show a) => Move a = Move a Symbol a deriving (Eq,Ord,Show)

data (Eq a,Ord a,Show a) => NFA a = NFA a [Move a] a deriving (Eq,Ord,Show)

states :: (Eq a,Ord a,Show a) => NFA a -> [a]
states (NFA s delta f) = (sort . nub) (s:f:rest)  
  where rest = [ s' | Move s' a t' <- delta ]
                 ++  
               [ t' | Move s' a t' <- delta ]

symbols :: (Eq a,Ord a,Show a) => NFA a -> [Symbol]
symbols (NFA s moves f) = (sort . nub) [ symb | Move s symb t <- moves ]

recog :: (Eq a,Ord a,Show a) => NFA a -> [Symbol] -> Bool
recog (NFA start moves final) [] = start == final
recog (NFA start moves final) (symbol:symbols) = 
  any (\ aut -> recog aut symbols) 
     [ NFA new moves final | 
           Move s symb new <- moves, s == start, symb == symbol ]

reachable :: (Eq a,Ord a,Show a) => NFA a -> [a]
reachable (NFA start moves final) = acc moves [start] [] 
  where 
  acc :: (Show a,Ord a) => [Move a] -> [a] -> [a] -> [a]
  acc moves [] marked = marked
  acc moves (b:bs) marked = acc moves (bs ++ (cs \\ bs)) (marked ++ cs) 
     where 
     cs  = nub [ c | Move b' symb c <- moves, b' == b, notElem c marked ]

accNFA :: (Eq a,Ord a,Show a) => NFA a -> NFA a
accNFA nfa@(NFA start moves final) = 
  if 
    notElem final fromStart 
  then 
    NFA start [] final
  else 
    NFA start moves' final
  where 
   fromStart = reachable nfa
   moves' = [ Move x symb y | Move x symb y <- moves, elem x fromStart ]

initPart :: (Eq a,Ord a,Show a) => NFA a -> [[a]]
initPart nfa@(NFA start moves final) = [states nfa \\ [final], [final]]

refinePart :: (Eq a, Ord a, Show a) => NFA a -> [[a]] -> [[a]]
refinePart nfa p = refineP nfa p p 
  where 
  refineP :: (Eq a, Ord a, Show a) => NFA a -> [[a]] -> [[a]] -> [[a]]
  refineP nfa part [] = []
  refineP nfa@(NFA start moves final) part (block:blocks) = 
     newblocks ++ (refineP nfa part blocks) 
       where 
         newblocks = 
           rel2part block (\ x y -> sameAccBl nfa part x y) 

sameAccBl :: (Eq a, Ord a, Show a) => NFA a -> [[a]] -> a -> a -> Bool
sameAccBl nfa part s t = 
    and [ accBl nfa part s symb == accBl nfa part t symb | 
                                               symb <- symbols nfa ]

accBl :: (Eq a, Ord a, Show a) => NFA a -> [[a]] -> a -> Symbol -> [[a]]
accBl nfa@(NFA start moves final) part s symb = 
   nub [ bl part y | Move x symb' y <- moves, symb' == symb, x == s ]

compress :: (Eq a, Ord a, Show a) => NFA a -> [[a]]
compress nfa = compress' nfa (initPart nfa)
  where 
  compress' :: (Eq a, Ord a, Show a) => NFA a -> [[a]] -> [[a]]
  compress' nfa part = if rpart == part 
                         then part 
                         else compress' nfa rpart 
   where rpart = refinePart nfa part 

minimalAut' :: (Eq a, Ord a, Show a) => NFA a -> NFA [a]
minimalAut' nfa@(NFA start moves final) = NFA start' moves' final'
  where 
   (NFA st mov fin) = accNFA nfa
   partition    = compress (NFA st mov fin) 
   f            = bl partition
   g (Acc ag)   = Acc ag
   g (Tst frm) = Tst (canonF frm) 
   start'       = f st
   final'       = f fin
   moves'       = (nub.sort) 
                     (map (\ (Move x y z) -> Move (f x) (g y) (f z)) mov)

convAut :: (Eq a,Ord a,Show a) => NFA a -> NFA State
convAut aut@(NFA s delta t) = 
    NFA 
    (f s) 
    (map (\ (Move x symb y) -> Move (f x) symb (f y)) delta)
    (f t) 
    where f = convert (states aut) 

minimalAut :: (Eq a, Ord a, Show a) => NFA a -> NFA State
minimalAut = convAut . minimalAut'

nullAut = (NFA 0 [] 1)

genKnown :: [Agent] -> NFA State
genKnown agents = (NFA 0 [Move 0 (Acc a) 1 | a <- agents ] 1)

relCknown :: [Agent] -> Form -> NFA State
relCknown agents form = (NFA 0 (Move 0 (Tst form) 1 :
                               [Move 1 (Acc a) 0 | a <- agents]) 0)

cKnown :: [Agent] -> NFA State
cKnown agents = (NFA 0 [Move 0 (Acc a) 0 | a <- agents] 0)

aut' :: (Show a,Ord a) => 
            PoAM -> State -> State -> NFA a -> NFA (State,Int,a)
aut' (Pmod sts pre acc _) s t (NFA start delta final) = 
  (NFA (s,0,start) delta' (t,1,final)) where 
    delta' = [ Move (u,1,w) (Acc a) (v,0,x) | 
                (a,u,v) <- acc, 
                Move w (Acc a') x <- delta,
                 a == a' ]
               ++
             [ Move (u,0,w) (Tst (table2fct pre u)) (u,1,w) |
                 u <- sts, 
                 w <- states (NFA start delta final) ]
               ++
             [ Move (u,1,v) 
                (Tst (Neg (Up (Pmod sts pre acc [u])
                                      (Neg form)))) (u,1,w) |
               u <- sts, 
               Move v (Tst form) w <- delta ]

aut :: (Show a,Ord a) => PoAM -> State -> State -> NFA a -> NFA State
aut am s t nfa = minimalAut (aut' am s t nfa)

tr' :: Form -> Form 
tr' Top = Top 
tr' (Prop p) = Prop p
tr' (Neg form) = Neg (tr' form)
tr' (Conj forms) = Conj (map tr' forms)
tr' (Disj forms) = Disj (map tr' forms)
tr' (K agent form) = K agent (tr' form) 
tr' (EK agents form) = Aut (genKnown agents) (tr' form)
tr' (CK agents form) = Aut (cKnown agents) (tr' form)

tr' (Aut nfa form) = Aut (tAut nfa) (tr' form)
tr' (Up (Pmod sts pre rel []) form) = Top
tr' (Up (Pmod sts pre rel [s]) Top) = Top 
tr' (Up (Pmod sts pre rel [s]) (Prop p)) = 
  impl (tr' (table2fct pre s)) (Prop p)
tr' (Up (Pmod sts pre rel [s]) (Neg form)) = 
  impl (tr' (table2fct pre s)) 
    (Neg (tr' (Up (Pmod sts pre rel [s]) form)))
tr' (Up (Pmod sts pre rel [s]) (Conj forms)) = 
  Conj [ tr' (Up (Pmod sts pre rel [s]) form) | form <- forms ]
tr' (Up (Pmod sts pre rel [s]) (Disj forms)) = 
  Disj [ tr' (Up (Pmod sts pre rel [s]) form) | form <- forms ]
tr' (Up (Pmod sts pre rel [s]) (K agent form)) =
  impl (tr' (table2fct pre s)) 
    (Conj [ K agent (tr' (Up (Pmod sts pre rel [t]) form)) | 
             t <- sts ]) 
tr' (Up (Pmod sts pre rel [s]) (EK agents form)) =
  tr' (Up (Pmod sts pre rel [s]) (Aut (genKnown agents) form))
tr' (Up (Pmod sts pre rel [s]) (CK agents form)) =
  tr' (Up (Pmod sts pre rel [s]) (Aut (cKnown agents) form))

tr' (Up (Pmod sts pre rel [s]) (Aut nfa form)) =
  Conj [ tr' (Aut (aut (Pmod sts pre rel [s]) s t  nfa) 
              (Up  (Pmod sts pre rel [t]) form)) |  t <- sts ]
tr' (Up (Pmod sts pre rel [s]) (Up (Pmod sts' pre' rel' points) form)) =
  tr' (Up (Pmod sts pre rel [s]) 
    (tr' (Up (Pmod sts' pre' rel' points) form)))
tr' (Up (Pmod sts pre rel points) form) = 
  Conj [ tr' (Up (Pmod sts pre rel [s]) form) | s <- points ]

kvbtr :: Form -> Form
kvbtr = canonF . tr'

tAut :: NFA State -> NFA State 
tAut (NFA s delta f) = NFA s (map trans delta) f
 where trans (Move u (Acc x) v)     = Move u (Acc x) v
       trans (Move u (Tst form) v) = Move u (Tst (kvbtr form)) v

