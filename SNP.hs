module SNP
where 
import DEMO
--Dynamic Epistemic MOdelling Tools, developed by Jan van Eijck

--This program implements Sum & Product problem in DEMO
--(Hans Freudenthal Version)

-- Two agens Mr. Sum and Mr. Product are represented by a/b.
-- Make sure to enable `last_agent = b' in line 28 of the DEMO source file.

--possible pairs 1<x<y, x+y<=100
pairs :: [(Int,Int)]
pairs  = [(x,y)|  x<-[2..100], y<-[2..100], x<y, x+y<=100]
--number of the possible worlds(pairs)
numpairs =llength(pairs)

--return the number of elements in a Data.List
llength [] =0
llength (x:xs) = 1+ llength xs

--indexed pairs, used for creating valuation
ipairs = zip [0..numpairs-1] pairs

--initial pointed epistemic model
msnp :: EpistM
msnp = (Pmod [0..numpairs-1] val acc [0..numpairs-1])
  where 
  val   = [ (w,[P x, Q y]) | (w,(x,y))<- ipairs]
  acc   = [(a,w,v)| (w,(x1,y1))<-ipairs, (v,(x2,y2))<-ipairs, x1+y1==x2+y2 ]++
              [(b,w,v)| (w,(x1,y1))<-ipairs, (v,(x2,y2))<-ipairs, x1*y1==x2*y2 ]
              
--Mr.Sum says: I knew that you didn't know the two numbers.
fmrs1 = K a (Conj [ Neg (K b (Conj [Prop (P x),Prop (Q y)]))| (x,y)<-pairs])
amrs1 = public (fmrs1)
----An equivalent representation requiring less computation:
fmrs1e = K a (Conj [Disj[Neg (Conj [Prop (P x),Prop (Q y)]), Neg (K b (Conj [Prop (P x),Prop (Q y)]))]| (x,y)<-pairs])
amrs1e = public (fmrs1e)

--Mr.Product says: Now I know the two numbers
fmrp2 = Disj [K b (Conj [Prop (P x),Prop (Q y)])|(x,y)<-pairs]
amrp2 = public (fmrp2)
----An equivalent representation again:
fmrp2e = Conj [(Disj[Neg (Conj [Prop (P x),Prop (Q y)]), K b (Conj [Prop (P x),Prop (Q y)]) ] )|(x,y)<-pairs] 
amrp2e = public (fmrp2e)

--Mr.Sum says: Now I know the two numbers too
fmrs3 = Disj [K a (Conj [Prop (P x),Prop (Q y)])|(x,y)<-pairs]
amrs3 = public (fmrs3)
----An equivalent representation again:
fmrs3e = Conj [(Disj[Neg (Conj [Prop (P x),Prop (Q y)]), K a (Conj [Prop (P x),Prop (Q y)]) ] )|(x,y)<-pairs] 
amrs3e = public (fmrs3e)

--This shows the solution of Sum & Product problem
solution = showM (upds msnp [amrs1e, amrp2e, amrs3e])
