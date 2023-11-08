
frobeniusOnWittTuple=method()
frobeniusOnWittTuple(ZZ,List):=(e,L)->(
if length unique apply(L,i->ring i) > 1 then return "error: all elements of tuple must live in the same ring";
p:=char ring first L;
for i in L list i^(p^e)
)




frobeniusOnWittRing=method()
