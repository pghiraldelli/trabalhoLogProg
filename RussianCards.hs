module RussianCards
where 

import DEMO

-- Contributed by Ji Ruan, revision and generalisation by Jan van Eijck

-- Make sure last_agent is set to c in Models 

deals = [((n0,n1,n2),(n3,n4,n5),n6) | n0 <- [0..6] :: [Int], 
                                      n1 <- [0..6] \\ [n0], 
                                      n2 <- [0..6] \\ [n0,n1], 
                                      n3 <- [0..6] \\ [n0,n1,n2], 
                                      n4 <- [0..6] \\ [n0,n1,n2,n3],
                                      n5 <- [0..6] \\ [n0,n1,n2,n3,n4], 
                                      n6 <- [0..6] \\ [n0,n1,n2,n3,n4,n5],
                                      n0 < n1, n1 < n2, 
                                      n3 < n4, n4 < n5 ]

indexed_deals = zip [0..139] deals

rus_init :: Integer -> EpistM 
rus_init n = Pmod [0..139] val acc [n]
    where 
      val = [ (i, [P n0, P n1, P n2, Q n3, Q n4, Q n5, R n6]) | 
              (i, ((n0,n1,n2),(n3,n4,n5),n6)) <- indexed_deals ]
      acc = [ (a,w,v) | (w,(d,_,_)) <- indexed_deals, 
                        (v,(e,_,_)) <- indexed_deals, d == e ]
            ++
            [ (b,w,v) | (w,(_,d,_)) <- indexed_deals, 
                        (v,(_,e,_)) <- indexed_deals, d == e ]
            ++
            [ (c,w,v) | (w,(_,_,d)) <- indexed_deals, 
                        (v,(_,_,e)) <- indexed_deals, d == e ]

a_knows_bs = 
  Conj[Disj[K a (Prop (Q i)), K a (Neg (Prop (Q i))) ] | i<- [0..6] ]

b_knows_as = 
  Conj[Disj[K b (Prop (P i)), K b (Neg(Prop (P i))) ] | i <- [0..6] ]

c_ignorant = 
  Conj[Conj[Neg (K c (Prop (P i))), Neg (K c (Prop (Q i))) ] 
             | i <- [0..6] ]

a_announce = public (K a (Disj[Conj[p0,p1,p2], 
                               Conj[p0,p3,p4], 
                               Conj[p0,p5,p6], 
                               Conj[p1,p3,p5], 
                               Conj[p2,p4,p6]]))

b_announce = public (K b r6) 

rus_1 = upd (rus_init 0) a_announce

check1 = isTrue rus_1 (CK [a,b,c] c_ignorant) 

check2 = isTrue rus_1 (CK [a,b] b_knows_as) 

rus_2 = upd rus_1 b_announce

check3 = isTrue rus_2 (CK [a,b,c] c_ignorant) 

check4 = isTrue rus_2 (CK [a,b] a_knows_bs) 

hand_a :: EpistM -> [Int]
hand_a pmod = [ i | i <- [0..6], isTrue pmod (K a (Prop (P i))) ]

hand2a_announce :: [Int] -> PoAM
hand2a_announce hand = public (K a (cmb2form $ dst hand)) where 
  cmb2form :: [(Int,Int,Int)] -> Form
  cmb2form triples = Disj 
    [ Conj [Prop (P n1),Prop (P n2), Prop (P n3)] | (n1,n2,n3) <- triples ]
  dst [x,y,z] = 
    (x,y,z) : zipWith (\ u (v,w) -> (u,v,w)) [x,x,y,z] (cb [x,y,z])
  cb :: [Int] -> [(Int,Int)]
  cb hand = dist ([0..6] \\ hand) where 
    dist [x,y,z,u] = [(x,y),(z,u),(x,z),(y,u)]

ms2a_announce :: EpistM -> PoAM
ms2a_announce pmod = hand2a_announce $ hand_a pmod 

ms2b_announce :: EpistM -> PoAM
ms2b_announce pmod = public (K b (Prop (R i))) where 
  [i] = [ j | j <- [0..6], isTrue pmod (K b (Prop (R j))) ]

gen_rus_1 :: Integer -> EpistM
gen_rus_1 n =  upd (rus_init n) (ms2a_announce (rus_init n))

gen_rus_2 :: Integer -> EpistM
gen_rus_2 n =  upd (gen_rus_1 n) (ms2b_announce (gen_rus_1 n))

gen_check1 :: State  -> Bool
gen_check1 n = isTrue (gen_rus_1 n) (CK [a,b,c] c_ignorant) 

gen_check2 :: State -> Bool
gen_check2 n = isTrue (gen_rus_1 n) (CK [a,b] b_knows_as) 

gen_check3 :: State -> Bool
gen_check3 n = isTrue (gen_rus_2 n) (CK [a,b,c] c_ignorant) 

gen_check4 :: State -> Bool 
gen_check4 n = isTrue (gen_rus_2 n) (CK [a,b] a_knows_bs) 

all_1 = all gen_check1 [0..139]
all_2 = all gen_check2 [0..139]
all_3 = all gen_check2 [0..139]
all_4 = all gen_check2 [0..139]

check_all = all_1 && all_2 && all_3 && all_4 

