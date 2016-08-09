module Caps
where 

import DEMO

-- in Models, set last_agent = d. 

capsInfo :: Form
capsInfo = Disj [Conj [f, g, Neg h, Neg j] | 
                       f <- [p1, p2, p3, p4], 
                       g <- [p1, p2, p3, p4] \\ [f],
                       h <- [p1, p2, p3, p4] \\ [f,g],
                       j <- [p1, p2, p3, p4] \\ [f,g,h], 
                       f < g, h < j                     ]

awarenessFirstCap  = info [b,c] p1
awarenessSecondCap = info [c]   p2

cK =  Disj [K c p3, K c (Neg p3)]
bK =  Disj [K b p2, K b (Neg p2)]

mo0  = upd (initE [P 1, P 2, P 3, P 4]) (test capsInfo)
mo1  = upd mo0 (public capsInfo)
mo2  = upds mo1 [awarenessFirstCap, awarenessSecondCap] 
mo3a = upd mo2 (public cK) 
mo3b = upd mo2 (public (Neg cK))

