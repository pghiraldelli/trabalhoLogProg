module DC
where 
import DEMO

-- code by Simona Orzan and Jan van Eijck

-- in Models, set last_agent = c. 

zero_or_one_payer =  
	(Disj [Conj [Neg p1, Neg p2, Neg p3],
               Conj [Neg p1, Neg p2, p3], 
	       Conj [Neg p1, p2, Neg p3], 
	       Conj [p1, Neg p2, Neg p3]    ])

dc1 = upd (initE [P 1, P 2, P 3, Q 1, Q 2, Q 3]) 
          (public zero_or_one_payer)

dc2 = upd dc1 (test 
  (Conj [Neg p1, p2, Neg p3, q1, q2, Neg q3]))

dc3 = upds dc2 [info [a] p1, info [b] p2, info [c] p3 ]

dc4 = upds dc3 [info [a,b] q1, info [b,c] q2, info [a,c] q3]

xor :: Form -> Form -> Form
xor x y = Neg (equiv x y) 

a_statement = public (xor (xor q1 q3) p1) 
b_statement = public (xor (xor q1 q2) p2)
c_statement = public (xor (xor q2 q3) p3)

dc5 = upds dc4 [a_statement, b_statement, c_statement]

gen_dc :: State -> EpistM 
gen_dc s = mod2pmod m [s] where m = fst (pmod2mp dc1) 

gen_dc_u s = 
  upds (gen_dc s) [info [a] p1, info [b] p2, info [c] p3,
                   info [a,b] q1, info [b,c] q2, info [a,c] q3, 
                   a_statement, b_statement, c_statement       ]

gen_check1 s = isTrue (gen_dc_u s)  
  (Conj [Neg p1 `impl` Conj [Neg (K a p2), Neg (K a p3)],
         Neg p2 `impl` Conj [Neg (K b p1), Neg (K b p3)],
         Neg p3 `impl` Conj [Neg (K c p1), Neg (K c p2)]])

gen_check2 s = 
  isTrue (gen_dc_u s) 
         (Disj [p1,p2,p3] `impl` CK [a,b,c] (Disj [p1,p2,p3]))

all_checks = all gen_check1 [0..31] && all gen_check2 [0..31]

