needsPackage "TestIdeals"
needsPackage "WittVectors"

Delta1=method()
Delta1(RingElement):=a->(
last wittOverringToTuple( wittTupleToOverring({a,0})-sum apply(terms a,i->wittTupleToOverring({i,0})))
)


fn=method()
fn(ZZ,RingElement):=(n,f)->(
p:=char ring f;
if n == 1 then return f^(p-1);
exponent := sum apply(toList(0..n-2),i->p^i);
f^(p-1)*Delta1(f^(p-1))^(exponent)
)

quasiFSplittingNumber=method()
quasiFSplittingNumber(Ideal,ZZ):=(I,max)->(
f:=product( I_*);
S:=ring I;
p:=char S;
m:=ideal gens S;
for i from 1 to max do if not isSubset(ideal fn(i,f) ,frobeniusPower(p^i,m)) then return i
)
