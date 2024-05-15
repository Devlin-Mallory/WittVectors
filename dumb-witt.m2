List ^ ZZ := (L, n) -> (
    if n <= 0 then( return {{}});
    output := apply(L, xx -> {xx});
    for i in 1..(n-1) do(
	output = (output**L);
	output = apply(output, toList);
	output = apply(output, flatten);
	);
    output
    )
	
dumbWitt = (n, R) -> (
    p := char R;
    d := numgens R;
    Rvars := flatten entries vars R;
    --- create indices for variables:
    baseIndices := apply(for i from 0 to d-1 list insert(i,1,toList(d-1:0)),j->{0}|{j});
    otherIndices := {};
    for i in 1..(n-1) do(
	newIndices := (toList(0..(p^i-1)))^d;
	newIndices = drop(newIndices, {0,0});
	newIndices = apply(newIndices, ind -> {i}|{ind});
	otherIndices = otherIndices | newIndices;
	    );
    allIndices := baseIndices | otherIndices;
    --- make ambient rings
    T := symbol T;
    A := ZZ[for i in allIndices list T_i, Degrees => for i in allIndices list i#0];
    B := QQ[for i in allIndices list T_i, Degrees => for i in allIndices list i#0];
    --- relations of Type 1
    --- note: the rings A and B get modified at each step. Is this actually faster? 
    for aa in n..(2*n-2) do(
	BtoA := map(A,B, vars A);
	relsB := flatten entries basis(aa, B);
	relsA := apply(relsB, xx -> BtoA(xx) );
	B = (flattenRing(B / ideal(relsB)))#0;
	A = (flattenRing(A / ideal(relsA)))#0;
	);
    for aa in 1..(n-1) do(
	BtoA := map(A,B, vars A);
	basisB := flatten entries basis(aa, B);
	relsB := apply(basisB, xx -> p^(n-aa)*xx);
	relsA := apply(relsB, xx -> BtoA(xx) );
	B = (flattenRing(B / ideal(relsB)))#0;
	A = (flattenRing(A / ideal(relsA)))#0;
	);
    BtoA := map(A,B, vars A);
    A = (flattenRing( (A / ideal( BtoA(p^n) )) ))#0;
    -- relations of Type 2
    if n <= 2 then( return A ) else(
	use A;
	relsGens := apply( select(otherIndices, indx -> indx#0 <= n-2),
	    xx -> p*T_xx - T_{xx#0 + 1, apply(xx#1, yy -> p*yy)}
	    );
	rels = ideal(relsGens);
	A = (flattenRing(A / rels) )#0;
	);
    --- output
    A
    )
--S := ZZ[T

end

loadPackage "WittVectors"
R = GF(3)[x,y]
WR = explicit (witt(2, R))
si = ideal WR
di = dumbWitt(R, 2)

phi = map(ring di, ring si, 

for xx in 0..19 do(
    print "-----------";
    print xx;
    print (flatten entries vars W)#xx;
    print (flatten entries vars D)#xx;
    --print (phi((flatten entries vars D)#xx) - (flatten entries vars W)#xx);
    )

---

phi = map(Da, Wa, first entries vars Da)
psi = map(Wa, Da, first entries vars Wa)

for ff in first entries gens ideal W do(
    print "------------------";
    print phi(ff);
    print (phi(ff) % ideal D == 0);
    )

for gg in first entries gens ideal D do(
    print "------------------";
    print psi(gg);
    print (psi(gg) % ideal W == 0);
    )

---
p = 2
n = 4
d = 2
R = GF(p)[x_1 .. x_d]
elapsedTime( dumbWitt(n, R) );
elapsedTime( explicit witt(n, R) );
