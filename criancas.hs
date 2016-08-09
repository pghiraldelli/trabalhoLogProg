import DEMO

criancas :: EpistM
criancas = ( Pmod [0..7] val acc [7] )
	where
		val = [ (0, [P 0, Q 0, R 0]), 
			(1, [P 0, Q 0, R 1]), 
			(2, [P 0, Q 1, R 0]), 
			(3, [P 0, Q 1, R 1]), 
			(4, [P 1, Q 0, R 0]), 
			(5, [P 1, Q 0, R 1]), 
			(6, [P 1, Q 1, R 0]),
			(7, [P 1, Q 1, R 1])]
		acc = [ (a , 0 , 4 ), (a , 1 , 5 ), (a , 2 , 6 ), (a , 3 , 7 ), (a , 4 , 0 ), (a , 5 , 1), (a , 6 , 2 ), (a , 7 , 3 ),
			(b , 0 , 2 ), (b , 6 , 4 ), (b , 7 , 5 ), (b , 3 , 1 ), (b , 2 , 0 ), (b , 4 , 6 ), (b , 5 , 7 ), (b , 1 , 3 ), 
			(c , 0 , 1 ), (c , 5 , 4 ), (c , 2 , 3 ), (c , 6 , 7 ), (c , 1 , 0 ), (c , 4 , 5 ), (c , 3 , 2 ), (c , 7 , 6 ) ]

anaSees = reveal[a][q0, q1, r0, r1]
betoSees = reveal[b][p0, p1, r0, r1]
carlaSees = reveal[c][p0, p1, q0, q1]

cr = upds criancas [anaSees, betoSees, carlaSees]

