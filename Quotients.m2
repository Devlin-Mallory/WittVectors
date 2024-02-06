wittOverringIdeal=method()
wittOverringIdeal(ZZ,Ideal):=(n,I)->(
    R:=ring I;
    d:=dim R;
    if class R =!= PolynomialRing then(
	error "expected an ideal in a polynomial ring";
	);
    trim ideal flatten for k from 0 to n -1 list (
	for j in I_* list wittTupleToOverring( toList(k:0_R)|{j}|toList(n-k-1:0_R) )
	)
    )



wittRingIdeal=method()
wittRingIdeal(ZZ,Ideal):=(n,I)->(
J:=wittOverringIdeal(n,I);
WR:=wittVectors(n,ring I);
Phi := WR.cache.overringMap;
 OR:=target Phi;
B:=quotient J;
kernelZZ((flattenRing(B))_1*map(B,ring J)*Phi)
)



testWittIdeal=method()
testWittIdeal(ZZ,ZZ,Ideal):=(d,n,I)->(
J := wittOverringIdeal(n,I);
f:=for i from 0 to n-1 list random(d,I);
isSubset(ideal wittTupleToOverring f,J)
)
