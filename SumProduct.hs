module SumProduct
where 

import DEMO

-- Program written by Ji Ruan

-- Make sure to set last_agent = b in Models

pairs :: [(Int,Int)]
pairs  = [ (x,y) |  x <- [2..100], y <- [2..100], x < y, x+y <= 100 ]

numpairs = toInteger (length pairs)

indexed_pairs = zip [0..numpairs-1] pairs

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

pform :: Int ->  Int -> Form
pform x y = Conj [Prop (P x), Prop (Q y)]

statement_1 = 
  Conj [ Neg (K b (pform x y)) | (x,y) <- pairs ]

statement_1e = 
  Conj [ pform x y `impl` Neg (K b (pform x y)) | (x,y) <- pairs ]

announcement_1 = public (K a statement_1e)

statement_2 = 
  Disj [ K b (pform x y) | (x,y) <- pairs ]

statement_2e = 
  Conj [ pform x y `impl` K b (pform x y) | (x,y) <- pairs ]

announcement_2 = public statement_2e

statement_3e =  
  Conj [ pform x y `impl` K a (pform x y) | (x,y) <- pairs ]

announcement_3 = public statement_3e

solution = showM (upds msnp [announcement_1,announcement_2,announcement_3])

