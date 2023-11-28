
verschiebung=method()
verschiebung(List):=L->(
if length unique apply(L,i->ring i) > 1 then return "error: all elements of tuple must live in the same ring";
{0_(ring first L)}|for i from 0 to length L -1  list L_i
)

verschiebung(RingElement):=F->(
B:=ring F;
if B.cache.?overringMap then return wittTupleToRing verschiebung(wittOverringToTuple(B.cache.overringMap(F))) 
else return wittTupleToOverring verschiebung(wittOverringToTuple(F))
)



