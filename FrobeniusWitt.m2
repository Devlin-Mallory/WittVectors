


frobenius(ZZ,RingElement) := (e,F)->(
B:=ring F;
-- make it take an element of WittOverringElement or similar
if B.cache.?overringMap then return wittTupleToRing frobeniusOnWitt(e,wittOverringToTuple(B.cache.overringMap(F))) 
else return wittTupleToOverring frobeniusOnWitt(e,wittOverringToTuple(F))
)



