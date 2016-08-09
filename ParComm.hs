module ParComm
where 
import DEMO

-- Make sure to set last_agent = b in DEMO

msnp :: EpistM
msnp = (Pmod [0..numpairs-1] val acc [0..numpairs-1])
  where 
  val   = [ (w,[P x, Q y]) | (w,(x,y)) <- indexed_pairs]
  acc   = [ (a,w,v) | (w,(x1,y1)) <- indexed_pairs, 
                      (v,(x2,y2)) <- indexed_pairs, 
                       x1+y1 == x2+y2                ]
          ++
          [ (b,w,v) | (w,(x1,y1)) <- indexed_pairs, 
                      (v,(x2,y2)) <- indexed_pairs, 
                       x1*y1 == x2*y2                ]
  pairs :: [(Int,Int)]
  pairs  = [ (x,y) |  x <- [2..100], y <- [2..100], x < y, x+y <= 100 ]
  numpairs = toInteger (length pairs)
  indexed_pairs = zip [0..numpairs-1] pairs

pair_at_index :: EpistM -> State -> (Int,Int) 
pair_at_index m i = (x,y) where 
  [P x,Q y] = table2fct (valuation m) i

pform :: Int ->  Int -> Form
pform x y = Conj [Prop (P x), Prop (Q y)]

p_statement_1 :: EpistM -> State -> Form 
p_statement_1 m i = 
  K a (Neg (K b (pform x y))) where (x,y) = pair_at_index m i

p_statement_2 :: EpistM -> State -> Form 
p_statement_2 m i = K b (pform x y) where (x,y) = pair_at_index m i

p_statement_3 :: EpistM -> State -> Form 
p_statement_3 m i = K a (pform x y) where (x,y) = pair_at_index m i

type PPoAM = Pmod State (EpistM -> State -> Form)

p_public :: (EpistM -> State -> Form) -> PPoAM
p_public f = 
   (Pmod [0] [(0,f)] [ (a,0,0) | a <- all_agents ] [0])

p_up :: EpistM -> PPoAM -> Pmod (State,State) [Prop]
p_up m@(Pmod worlds val acc points) pam@(Pmod states ppre susp actuals) = 
   Pmod worlds' val' acc' points'
   where 
   worlds' = [ (w,s) | w <- worlds, s <- states, 
                       f <- maybe [] (\ x -> [x]) (lookup s ppre), 
                       isTrAt w m (f m w)                      ] 
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

p_upd ::  EpistM -> PPoAM -> EpistM
p_upd sm pam = (bisimPmod (sameVal) . convPmod) (p_up sm pam)

p_upds  :: EpistM -> [PPoAM] -> EpistM
p_upds = foldl p_upd 

p_solution = showM (p_upds msnp [p_public p_statement_1, 
                                 p_public p_statement_2,
                                 p_public p_statement_3])

