module SecCom
where 

import DEMO

-- in Models, set last_agent = c. 

link_ab_pq = ndSum (groupM [a,b] (equiv p q)) 
                   (groupM [a,b] (equiv p (Neg q)))
c_b_pq = CK [a,b] (Disj [K b (p `equiv` q), K b (p `equiv` (Neg q))])
ck_ab_link = Disj [CK [a,b] (p `equiv` q), CK [a,b] (p `equiv` (Neg q))]
k_tr   = K a (Neg (K b p)) `impl` Neg (K b p)

aKq = Disj [K a q, K a (Neg q)]
bKq = Disj [K b q, K b (Neg q)]
cKq = Disj [K c q, K c (Neg q)]

mo0 = initE [P 0, Q 0]
mo1 = upds mo0 [info [a] p,link_ab_pq]
mo2 = upd mo1 (public p) 

