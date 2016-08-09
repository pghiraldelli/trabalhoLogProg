module UpdateSem 

where 

import DEMO

-- make sure to set last_agent = a in Models

fact_update :: Form -> PoAM 
fact_update form = public form

may_update :: Form -> PoAM
may_update form = public (Neg (K a (Neg form)))

m0 = initE [P 0, Q 0, R 0]

example1 = upds m0 [may_update r, fact_update (Neg r)]

example2 = upds m0 [fact_update r, may_update (Neg r)]

