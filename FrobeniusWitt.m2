
frobeniusOnWitt=method()
frobeniusOnWitt(ZZ,List):=(e,L)->(
if length unique apply(L,i->ring i) > 1 then return "error: all elements of tuple must live in the same ring";
p:=char ring first L;
for i in L list i^(p^e)
)

frobeniusOnWitt(ZZ,RingElement):=(e,F)->(
B:=ring F;
if B.cache.?overringMap then return wittTupleToRing frobeniusOnWitt(e,wittOverringToTuple(B.cache.overringMap(F))) 
else return wittTupleToOverring frobeniusOnWitt(e,wittOverringToTuple(F))
)



