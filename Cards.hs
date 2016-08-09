module Cards
where 

import DEMO

-- in Models, set last_agent = c. 

cards0 :: EpistM
cards0 = (Pmod [0..5] val acc [0])
  where 
  val    = [(0,[P 1,Q 2,R 3]),(1,[P 1,R 2,Q 3]),
            (2,[Q 1,P 2,R 3]),(3,[Q 1,R 2,P 3]),
            (4,[R 1,P 2,Q 3]),(5,[R 1,Q 2,P 3])]
  acc    = [(a,0,0),(a,0,1),(a,1,0),(a,1,1),
            (a,2,2),(a,2,3),(a,3,2),(a,3,3),
            (a,4,4),(a,4,5),(a,5,4),(a,5,5),
            (b,0,0),(b,0,5),(b,5,0),(b,5,5),
            (b,2,2),(b,2,4),(b,4,2),(b,4,4),
            (b,3,3),(b,3,1),(b,1,3),(b,1,1),
            (c,0,0),(c,0,2),(c,2,0),(c,2,2),
            (c,3,3),(c,3,5),(c,5,3),(c,5,5),
            (c,4,4),(c,4,1),(c,1,4),(c,1,1)]

showABp :: PoAM
showABp = (Pmod [0,1] pre susp [0])
  where
  pre  = [(0,p1),(1,q1)]
  susp = [(a,0,0),(a,1,1),
          (b,0,0),(b,1,1),
          (c,0,0),(c,0,1),
          (c,1,0),(c,1,1)]

revealAB = reveal [b] [p1,q1,r1]

result   = upd cards0 revealAB

