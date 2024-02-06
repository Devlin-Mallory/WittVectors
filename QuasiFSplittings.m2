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

u = method()
u(ZZ,RingElement) :=(e,f)->(
S:=ring f;
if class S =!= PolynomialRing then error "needed an element of a polynomial ring";
n:=numgens S;
p:=char S;
termsf := terms f;
--exponentsf := flatten apply(termsf, exponents);
sum apply( select(termsf, i-> ((flatten exponents i) % p^e) == toList(n:p^e-1)), i-> (last coefficients(i)  ) * S_(flatten exponents(i)//p^e))
)

theta=method()
theta(RingElement,RingElement):= (f,a) ->(
p:=char ring f;
u(1,Delta1(f^(p-1))*a)
)
