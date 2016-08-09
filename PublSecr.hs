module PublSecr 
where 

import DEMO

-- set last_agent = c in Models

ms1 = upds (initE [P 1, P 2, Q 0]) 
 [test (Conj [p1,(Neg p2),q]),info [b] p2,info [a] p1,info [a] q]

ms2 = upd ms1 (public ((Neg p2) `impl` q))

