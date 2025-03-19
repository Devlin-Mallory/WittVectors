
verschiebung(RingElement):=F->(
B:=ring F;
if B.cache.?overringMap then return wittTupleToRing verschiebung(wittOverringToTuple(B.cache.overringMap(F))) 
else return wittTupleToOverring verschiebung(wittOverringToTuple(F))
)



