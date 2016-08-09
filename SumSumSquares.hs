module SumSumSquares
where 

import DEMO

-- Make sure to set last_agent = b in Models

pairs :: [(Int,Int)]
pairs  = [ (x,y) |  x <- [1..20], y <- [1..20], x <= y ]

numpairs = toInteger (length pairs)

indexed_pairs = zip [0..numpairs-1] pairs

msss :: EpistM
msss = (Pmod [0..numpairs-1] val acc [0..numpairs-1])
  where 
  val   = [ (w,[P x, Q y]) | (w,(x,y)) <- indexed_pairs]
  acc   = [ (a,w,v) | (w,(x1,y1)) <- indexed_pairs, 
                      (v,(x2,y2)) <- indexed_pairs, 
                       x1^2+y1^2 == x2^2+y2^2        ]
          ++
          [ (b,w,v) | (w,(x1,y1)) <- indexed_pairs, 
                      (v,(x2,y2)) <- indexed_pairs, 
                       x1+y1 == x2+y2                ]

pform :: Int ->  Int -> Form
pform x y = Conj [Prop (P x), Prop (Q y)]

not_knows_a = 
  Conj [ pform x y `impl` Neg (K a (pform x y)) | (x,y) <- pairs ]
not_knows_b = 
  Conj [ pform x y `impl` Neg (K b (pform x y)) | (x,y) <- pairs ]

knows_a = 
  Conj [ pform x y `impl` K a (pform x y) | (x,y) <- pairs ]

solution = showM (upds msss [public not_knows_a, 
                             public not_knows_b,
                             public not_knows_a,
                             public not_knows_b,
                             public not_knows_a,
                             public not_knows_b,
                             public knows_a ])

variation1 = showM (upds msss [public not_knows_a, 
                               public not_knows_b,
                               public not_knows_a,
                               public not_knows_b,
                               public knows_a ])

knows_b = 
  Conj [ pform x y `impl` K b (pform x y) | (x,y) <- pairs ]

variation2 = showM (upds msss [public not_knows_a,
                               public not_knows_b, 
                               public not_knows_a,
                               public not_knows_b, 
                               public not_knows_a,
                               public knows_b ])

