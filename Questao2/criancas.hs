import DEMO

criancas :: EpistM
criancas = ( Pmod [0..7] val acc [3] )
	where
		val = [ (0, [P 0, Q 0, R 0]), 
			(1, [P 0, Q 0, R 1]), 
			(2, [P 0, Q 1, R 0]), 
			(3, [P 0, Q 1, R 1]), 
			(4, [P 1, Q 0, R 0]), 
			(5, [P 1, Q 0, R 1]), 
			(6, [P 1, Q 1, R 0]),
			(7, [P 1, Q 1, R 1])]
		acc = [ (a , 0 , 0 ), (a , 1 , 1 ), (a , 2 , 2 ), (a , 3 , 3 ), (a , 4 , 4 ), (a , 5 , 5 ), (a , 6 , 6 ), (a , 7 , 7 ), (a , 0 , 4 ), (a , 1 , 5 ), (a , 2 , 6 ), (a , 3 , 7 ), (a , 4 , 0 ), (a , 5 , 1), (a , 6 , 2 ), (a , 7 , 3 ),
			(b , 0 , 0 ), (b , 1 , 1 ), (b , 2 , 2 ), (b , 3 , 3 ), (b , 4 , 4 ), (b , 5 , 5 ), (b , 6 , 6 ), (b , 7 , 7 ), (b , 0 , 2 ), (b , 6 , 4 ), (b , 7 , 5 ), (b , 3 , 1 ), (b , 2 , 0 ), (b , 4 , 6 ), (b , 5 , 7 ), (b , 1 , 3 ), 
			(c , 0 , 0 ), (c , 1 , 1 ), (c , 2 , 2 ), (c , 3 , 3 ), (c , 4 , 4 ), (c , 5 , 5 ), (c , 6 , 6 ), (c , 7 , 7 ), (c , 0 , 1 ), (c , 5 , 4 ), (c , 2 , 3 ), (c , 6 , 7 ), (c , 1 , 0 ), (c , 4 , 5 ), (c , 3 , 2 ), (c , 7 , 6 ) ]

sussurroPai :: PoAM
sussurroPai = ( Pmod[0..1] pre acc [0])
	where 
		pre = [(0, Neg(Conj[p0, q0, r0])), (1, Conj[p0, q0, r0])]
		acc = [(a, 0, 0), (a, 1, 1),
			(b, 0, 0), (b, 0, 1), (b, 1, 0), (b, 1, 1),
			(c, 0, 0), (c, 0, 1), (c, 1, 0), (c, 1, 1)]

aposSussurro = upd criancas sussurroPai

alguemSabe = Disj[Disj[K a p0, K b q0, K c r0], Disj[K a p1, K b q1, K c r1]]

anuncio :: EpistM -> EpistM
anuncio modelo = 
	if isTrue modelo (alguemSabe)
		then modelo
	else
		upd modelo (public (Neg (alguemSabe)))

--anuncio True = m p
--anuncio False = upd m public (Neg (p))

pergunta1 = anuncio aposSussurro
pergunta2 = anuncio pergunta1
pergunta3 = anuncio pergunta2
