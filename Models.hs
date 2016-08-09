module Models where 

import Data.List 

data Agent = A | B | C | D | E deriving (Eq,Ord,Enum) 

a, alice, b, bob, c, carol, d, dave, e, ernie  :: Agent 
a = A; alice = A
b = B; bob   = B
c = C; carol = C
d = D; dave  = D
e = E; ernie = E

instance Show Agent where 
  show A = "a"; show B = "b"; show C = "c"; show D = "d" ; show E = "e"

all_agents :: [Agent]
all_agents = [a .. last_agent]

last_agent :: Agent 
--last_agent = a
--last_agent = b
--last_agent = c
last_agent = d
--last_agent = e

data Model state formula = Mo
                           [state]
                           [(state,formula)]
                           [(Agent,state,state)]
                           deriving (Eq,Ord,Show)

data Pmod state formula = Pmod
                           [state]
                           [(state,formula)]
                           [(Agent,state,state)]
                           [state]
                           deriving (Eq,Ord,Show)

mod2pmod :: Model state formula -> [state] -> Pmod state formula
mod2pmod (Mo states prec accs) points = Pmod states prec accs points 

pmod2mp :: Pmod state formula -> (Model state formula, [state]) 
pmod2mp (Pmod states prec accs points)  = (Mo states prec accs, points)

decompose ::  Pmod state formula -> [(Model state formula, state)]
decompose (Pmod states prec accs points) = 
   [(Mo states prec accs, point) | point <- points ]

table2fct :: Eq a => [(a,b)] -> a -> b
table2fct t = \ x -> maybe undefined id (lookup x t)

rel2part :: (Eq a) => [a] -> (a -> a -> Bool) -> [[a]]
rel2part [] r = []
rel2part (x:xs) r = xblock : rel2part rest r
  where 
  (xblock,rest) = partition (\ y -> r x y) (x:xs)

domain :: Model state formula -> [state]
domain (Mo states _ _) = states

eval :: Model state formula -> [(state,formula)]
eval (Mo _ pre _) = pre

access :: Model state formula -> [(Agent,state,state)]
access (Mo _ _ rel) = rel

points :: Pmod state formula -> [state]
points (Pmod _ _ _ pnts) = pnts

gsm :: Ord state => Pmod state formula ->  Pmod state formula
gsm (Pmod states pre rel points) = (Pmod states' pre' rel' points)
   where 
   states' = closure rel all_agents points
   pre'    = [(s,f)     | (s,f)     <- pre, 
                           elem s states'                   ]
   rel'    = [(ag,s,s') | (ag,s,s') <- rel, 
                           elem s states', 
                           elem s' states'                  ]

closure ::  Ord state => 
             [(Agent,state,state)] -> [Agent] -> [state] -> [state]
closure rel agents xs 
  | xs' == xs = xs
  | otherwise = closure rel agents xs'
     where 
     xs' = (nub . sort) (xs ++ (expand rel agents xs))

expand :: Ord state => 
           [(Agent,state,state)] -> [Agent] -> [state] -> [state]
expand rel agnts ys = 
      (nub . sort . concat) 
         [ alternatives rel ag state | ag    <- agnts, 
                                       state <- ys       ]

alternatives :: Eq state => 
                [(Agent,state,state)] -> Agent -> state -> [state]
alternatives rel ag current = 
  [ s' | (a,s,s') <- rel, a == ag, s == current ] 

