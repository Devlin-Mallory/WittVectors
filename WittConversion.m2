wittOverring = method()
wittTupleToOverring = method()
wittVectors=method()
wittTupleToRing = method()
wittRingToTuple=method()
wittOverringToTuple = method()
wittRingIdeal=method()
wittOverringIdeal=method()

-----------------------------
-----------------------------
-----------------------------

-- EAMON, 8/26/2025: I have fixed this so that the wittOverring of a quotient ring
-- is the wittOverring of its ambient ring. From the point of view of arithmetic, I
-- don't think this will break anything, but we should test.


wittOverring(ZZ, Ring) := (n, R) -> (
    if class R =!= PolynomialRing then(
        S := ambient R;
        if class S =!= PolynomialRing then(
	    error "wittVectors currently only implemented for quotients of polynomial rings"
	    );
	OS := wittOverring(n, S);
	OSvars := flatten entries vars OS;
	WittSub := map(OS, R, OSvars); -- WARNING: not a real map!
	OS.cache.wittSub = WittSub;
	OS.cache.unWitt = R;
	return(OS)
	);
    if class R === PolynomialRing then(
        Rvars := flatten entries vars R;
        p := char R;
        d := length Rvars;
        -- we create the WittOverring; called so because the n-th Witt ring of R
        -- will be a subring of this WittOverring.
        T := symbol T;
	OR := ZZ[T_1 .. T_d] / p^n;
	OR.cache = new CacheTable;
	ORvars := flatten entries vars OR;
	WittSub = map(OR, R, ORvars); -- WARNING: this is not a "real" map!
	OR.cache.wittSub = WittSub;
	OR.cache.unWitt = R;
	return(OR)
	);
)


--OLD VERSION

-- wittOverring(ZZ, Ring) := (n, R) -> (
--     --TODO: for a quotient ring R, test wittSub of its overring.
--     if class R =!= PolynomialRing then(
--         S := ambient R; 
--         --TODO: flattenRing S before checking its polynomial?
--         if class S =!= PolynomialRing then(
-- 	    error "wittVectors currently only implemented for quotients of polynomial rings"
-- 	    );
--         I:=ideal R;
-- 	OR := quotient wittOverringIdeal(n, I);
-- 	OR.cache = new CacheTable;
-- 	ORvars := flatten entries vars OR;
-- 	WittSub := map (OR, R, ORvars); -- WARNING: not a real map!
-- 	OR.cache.wittSub = WittSub;
--         OR.cache.unWitt = R;);
--     if class R === PolynomialRing then(
--         Rvars := flatten entries vars R;
--         p := char R;
--         d := length Rvars;
--         -- we create the WittOverring; called so because the n-th Witt ring of R
--         -- will be a subring of this WittOverring.
--         T := symbol T;
-- 	OR = ZZ[T_1 .. T_d] / p^n;
-- 	OR.cache = new CacheTable;
-- 	ORvars = flatten entries vars OR;
-- 	WittSub = map(OR, R, ORvars); -- WARNING: this is not a "real" map!
-- 	OR.cache.wittSub = WittSub;
-- 	OR.cache.unWitt = R;);
--     OR
-- )

-----------------------------
-----------------------------
-----------------------------

wittTupleToOverring(WittRingElement) := w -> (
    W := ring w;
    R := W.unWitt;
    n := W.wittLength;
    p := char R;
    OR := W.overring;
    WittSub := OR.cache.wittSub;
    WittLL := apply(toList(w), ff -> WittSub(ff));
    sum toList apply(0..(n-1), j -> p^j*(WittLL#j)^(p^(n-1-j)) )
    )

-----------------------------
-----------------------------
-----------------------------

wittVectors(ZZ,Ring):=(n,R)->(
    --if n == 1 then return R;
    --check if R is polynomial ring
    if class R =!= PolynomialRing then( 
        S := ambient R; 
        --TODO: flattenRing S before checking its polynomial?
        if class S =!= PolynomialRing then( error "wittVectors currently only implemented for quotients of polynomial rings");
        I:=ideal R; 
        quotient wittRingIdeal(n,I)
    );
    --
    p := char R;
    d := numgens R; -- number of variables
    baseVariables := apply(for i from 0 to d-1 list insert(i,1,toList(d-1:0)),j->{0}|{j});
    -- cubes is the list of indices; 
    -- T_{n,{a_1..a_d}} corresponds to p^n * x_1^{a_1/p^n}..x_d^{a_n/p^n}
    cubes := baseVariables| sort select( flatten for i from 1 to n-1 list apply(flatten \ entries \ latticePoints hypercube(d, 0, p^(i) - 1),j->{i}|{j}), i->last i != toList(d:0));
    T := symbol T;
    A := ZZ[for i in cubes list T_i]/p^n;
    t := symbol t;
    --t_i is x_i^(1/p^n)
    --B := ZZ[t_0..t_(d-1)]/p^n;
    wittR := witt(n,R);
    B:=wittR.overring;
    L := for i in cubes list p^(first i)*(product for j from 0 to d - 1 list B_j^((last i)_j*p^(n-first i -1)));
    aA := ambient A;
    iA := ideal A;
    K := kernelZZ map(B, A, L);
    aK := sub(K, aA);
    WR := quotient (iA + aK);
    Phi := map(B,WR,L);
    --cache overringMap and unWitt
    WR.cache.overringMap=Phi;
    WR.cache.unWitt = R;
    WR
    )

-----------------------------
-----------------------------
-----------------------------

wittVectors(ZZ,RingMap) := (n,f)->(
(WT,WS):=(wittVectors(n,target f),wittVectors(n, source f));
L:= for i in gens WS list wittTupleToRing witt(f \ (wittRingToTuple(i)));
map(WT,WS,L)
)

-----------------------------
-----------------------------
-----------------------------

wittTupleToRing(WittRingElement):= w-> (
    W := ring w;
    n := W.wittLength;
    --if n == 1 then return first L;
    L := w.tuple;
    R := W.unWitt;
    p := char R;
    WR := explicit W;
    use R;
    G:=wittTupleToOverring(w);
    Phi := WR.cache.overringMap;
    --print G;
    sum for m in terms G list(
	if degree m == {0} then sub(m,source Phi) else(
	    (B,pi):=flattenRing quotient ideal m;
	    --the below method doesn't always work to find a preimage... we should figure out a better way    
	    preimages := (kernelZZ(pi*map(source pi,WR,Phi)))_*;
	    multiplied:=flatten for i in preimages list for j from 1 to p^n-1 list i*j;
	    first select(multiplied,i->Phi(i)==m)
	    )    
	)
    --G//Phi(vars source Phi)
    )

-----------------------------
-----------------------------
-----------------------------

wittRingToTuple(RingElement):=(F)->(
    WR:=ring F;
    Phi:=WR.cache.overringMap;
    wittOverringToTuple(Phi(F))
)

-----------------------------
-----------------------------
-----------------------------


    takeRoot := (f, n) -> (
    --- in a ring of char p , takes the (1/p^n) root of a polynomial f
    R := ring f;
    p := char R;
    d := numgens R;
    S := ambient R;
    yy := symbol yy;
    SY := S[yy_0 .. yy_(d-1)] / ideal( for i from 0 to d-1 list yy_i^(p^n) - S_i );
    Ssub := map( SY, S, toList( yy_0..yy_(d-1)) );
    RY := quotient Ssub(ideal R);
    Rsub := (last flattenRing(RY))*map(RY,R,Ssub);
    sub(Rsub(f),R)
    );


wittOverringToTuple(RingElement) := F -> (
    OR := ring F;
    R := OR.cache.unWitt;
    unWittSub := map(R, OR, vars R); -- WARNING!! Fix when working with arbitrary finite fields?
    wittSub := OR.cache.wittSub;
    (p, n) := toSequence (factor(char OR))#0;
    
    if n == 1 then(
	return witt{ unWittSub(F) });
    WR1 := witt(n-1, R); 
    OR1 := WR1.overring;
    wittReduce := map( OR1, OR, vars OR1);
    
    F0 := F % ideal(sub(p, OR));
    f0 := takeRoot( unWittSub(F0), n-1 );
    
    nextF := wittReduce( ( F - (wittSub f0)^(p^(n-1)) ) // p);
    witt{f0} | wittOverringToTuple( nextF )
    )

-----------------------------
-----------------------------
-----------------------------

wittRingToTuple(Ideal) := I -> (
    Igens := flatten entries gens I;
    wittgens := apply(Igens, wittRingToTuple);
    wittIdeal(wittgens)
    )


-----------------------------
-----------------------------
-----------------------------

wittOverringIdeal(ZZ,Ideal):=(n,I)->(
    R:=ring I;
    d:=dim R;
    if class R =!= PolynomialRing then(
	error "expected an ideal in a polynomial ring";
	);
    --trim
    ideal flatten for k from 0 to n -1 list (
	for j in I_* list wittTupleToOverring witt( toList(k:0_R)|{j}|toList(n-k-1:0_R) )
	)
    )

-----------------------------
-----------------------------
-----------------------------

wittRingIdeal(ZZ,Ideal):=(n,I)->(
J:=wittOverringIdeal(n,I);
WittR := witt(n, ring I);
WR:=explicit WittR;
Phi := WR.cache.overringMap;
OR:=target Phi;
B:=quotient J;
kernelZZ((flattenRing(B))_1*map(B,ring J)*Phi)
)


end


------------------
----------- This will be eventually deleted, but please leave while we figure out why witt is slow for WittQuotientRings
------------------

S = (ZZ/5)[x,y,z]
gg = random(4, S)

n = 4

k = 0
wll0 = toList(k:0_S) | {gg} | toList(n-k-1:0_S)
ww0 = witt(wll0)
wov0 = wittTupleToOverring ww0

k = 1
wll1 = toList(k:0_S) | {gg} | toList(n-k-1:0_S)
ww1 = witt(wll1)
wov1 = wittTupleToOverring ww1

k = 2
wll2 = toList(k:0_S) | {gg} | toList(n-k-1:0_S)
ww2 = witt(wll2)
wov2 = wittTupleToOverring ww2

k = 3
wll3 = toList(k:0_S) | {gg} | toList(n-k-1:0_S)
ww3 = witt(wll3)
wov3 = wittTupleToOverring ww3



--
wll = toList(k:0_S) | {gg} | toList(n-k-1:0_S) 
ww = witt(wll)




elapsedTime wittTupleToOverring(ww);

wittTupleToOverring(WittRingElement) := w -> (
    W := ring w;
    R := W.unWitt;
    n := W.wittLength;
    p := char R;
    OR := W.overring;
    WittSub := OR.cache.wittSub;
    WittLL := apply(toList(w), ff -> WittSub(ff));
    sum toList apply(0..(n-1), j -> p^j*(WittLL#j)^(p^(n-1-j)) )
    )
