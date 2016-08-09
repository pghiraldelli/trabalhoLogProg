import DEMO

myread :: PoAM
myread = ( Pmod [0..1] pre acc [1] )
	where
		pre = [ ( 0, Neg p ) , ( 1, p )]
		acc = [ (a , 0 , 0 ) ,  ( a, 1 , 1 ) , ( b , 0 , 0 ) , ( b , 0 , 1 ) , ( b , 1 , 0 ) , ( b , 1 , 1 ) , ( c , 0 , 0 ) , ( c , 0 , 1 ) , ( c , 1 , 0 ) , ( c , 1 , 1 ) ]

mm1 :: EpistM
mm1 = initE [P 0,Q 0] 
mm2 = upd ( mm1 ) (myread)
mm3 = upd ( mm1 ) ( message a p )

