module Muddy
where

import DEMO

-- in Models, set last_agent = d. 

bcd_dirty = Conj [Neg p1, p2, p3, p4]

awareness = [info [b,c,d] p1, 
             info [a,c,d] p2,
             info [a,b,d] p3, 
             info [a,b,c] p4 ]

aK =  Disj [K a p1, K a (Neg p1)]
bK =  Disj [K b p2, K b (Neg p2)]
cK =  Disj [K c p3, K c (Neg p3)]
dK =  Disj [K d p4, K d (Neg p4)]

mu0 = upd (initE [P 1, P 2, P 3, P 4]) (test bcd_dirty)
mu1 = upds mu0 awareness 
mu2 = upd  mu1 (public (Disj [p1, p2, p3, p4])) 
mu3 = upd  mu2 (public (Conj[Neg aK, Neg bK, Neg cK, Neg dK]))
mu4 = upd  mu3 (public (Conj[Neg aK, Neg bK, Neg cK, Neg dK]))
mu5 = upds mu4 [public (Conj[bK, cK, dK])]

