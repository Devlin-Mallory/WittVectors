--here's where we'll define classes and class operations

needsPackage "TestIdeals"
witt = method()
explicit = method()
explicitOver = method()
wittIdeal = method(Dispatch => Thing)

---
--- WittRingElement
---
WittRingElement = new Type of MutableHashTable;

protect tuple;
witt(List) := L0->(
    ww := new WittRingElement from MutableHashTable;
    --check all elements of the list lie in ZZ or same ring
    L := apply(L0,i->ring i);
    BaseRing := unique select(L,i-> i =!= ZZ);
    if  length (BaseRing) > 1 then error "expected elements from the same ring";
    --
    ww.tuple = apply(L0,i -> sub(i, first BaseRing ));
    return ww
)

net(WittRingElement) := w -> net(w.tuple)

toList(WittRingElement) := w -> w.tuple

--TODO: here I would like R = GF(3)[x]; W = witt(2, R); w = witt({x, x+1}); ring w
-- to return W instead of Witt_2(R). Tried to do it with caching below but failed. 
--
--
ring(WittRingElement) := W -> (
    R := ring(W.tuple#0); -- note that witt subs every entry into R so this is good enough
    n := length W;
    witt(n, R)
    )

-- cache version: does not work.
--ring(WittRingElement) := W -> (
--    R := ring(W#0);
--    n := length W;
--    if not R.cache.wittRings#n then(
--	return witt(length W, ring(W#0));
--	) else (
--	return R.cache.wittRings#n;
--	);
--)

length WittRingElement := ww -> (
    length ww.tuple
    )

WittRingElement + WittRingElement := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if (ring w1) =!= (ring w2) then error "expected vectors over the same ring";
    w1over := explicitOver(w1);
    w2over := explicitOver(w2);
    outputover := w1over + w2over;
    wittOverringToTuple outputover
    )

- WittRingElement := ww -> (
    newtuple := apply(ww.tuple, xx -> -xx);
    witt(newtuple)
    )

WittRingElement - WittRingElement := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if ring w1 =!= ring w2 then error "expected vectors over the same ring";
    w1 + (-w2)
    )
    
ZZ * WittRingElement := (nn, ww) -> (
    wwover := explicitOver(ww);
    wittOverringToTuple(nn*wwover)
    )

WittRingElement * ZZ := (ww, nn) -> (
    wwover := explicitOver(ww);
    wittOverringToTuple(nn*wwover)
    )

WittRingElement * WittRingElement := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if ring w1 =!= ring w2 then error "expected elements of the same ring";
    w1over := explicitOver(w1);
    w2over := explicitOver(w2);
    outputover := w1over * w2over;
    wittOverringToTuple outputover
    )

WittRingElement ^ ZZ := (ww, nn) -> (
    wwover := explicitOver(ww);
    outputover := wwover^nn;
    wittOverringToTuple outputover
    )

WittRingElement | WittRingElement := (w1, w2) -> (
    witt(w1.tuple | w2.tuple)
    )

WittRingElement == WittRingElement := (w1, w2) -> (
    w1.tuple == w2.tuple
    )

frobenius(WittRingElement) := ww -> (
    witt frobeniusOnWitt(1,ww.tuple)
    )

frobenius(ZZ, WittRingElement) := (nn,ww) -> (
    witt frobeniusOnWitt(nn, ww.tuple)
    )

verschiebung(WittRingElement) := ww -> (
    witt verschiebung(ww.tuple)
    )

explicit(WittRingElement) := w -> (
    if not w.?explicit then( 
	w.explicit = wittTupleToRing(w.tuple);
	);
    w.explicit
    )

explicitOver(WittRingElement) := ww -> (
    if not ww.?explicitOver then(
	ww.explicitOver = wittTupleToOverring(ww.tuple);
	);
    ww.explicitOver
    )

-- Crop Witt vector to have a given length. We want that because that will allow us to add/multiply Witt vectors of different lengths by cropping the longer one.

CropWittVector = method ()
CropWittVector(WittRingElement,ZZ):= (w,n)->(
    if length w<n then error "Can't crop to something longer";
    L:={};
    for i from 0 to n-1 do {
        L_i:=w_i;-- there is an issue here with lists being unmutable
    };
    return witt L;
)

subInWittRing = method()
subInWittRing(List,RingElement) := (L,f) -> (
Lrings := unique apply(L,ring);
if length Lrings > 1 then error "expected all WittRingElements to live in the same ring";
Lexplicit := apply(L,explicitOver);
wittOverringToTuple(sub(f, matrix{Lexplicit}))
)


-------------------------------
-------------WittPolynomialRing
-------------------------------

WittPolynomialRing = new Type of MutableHashTable;

protect wittLength
protect overring

witt(ZZ,PolynomialRing) := (n,R)->(
    if not R.?cache then(
	R.cache = new CacheTable;
	);
    if not R.cache.?wittRings then(
	R.cache.wittRings = new CacheTable;
	);
    if not R.cache.wittRings#?n then(
	W := new WittPolynomialRing from MutableHashTable;
	W.wittLength = n;
	W.unWitt = R;
	W.overring = wittOverring(n,R);
	R.cache.wittRings#n = W;
	);
    R.cache.wittRings#n
)

net(WittPolynomialRing) := WPR->(
	return horizontalJoin("Witt", (net(WPR.wittLength))^-1, "(", net WPR.unWitt, ")");
)

explicit(WittPolynomialRing) := WPR->(
	if (not WPR.?explicit) then(
		WPR.explicit = wittVectors(WPR.wittLength, WPR.unWitt);
	);
	return WPR.explicit;
)

explicitOver(WittPolynomialRing) := WPR -> (
    -- make cache!
    WPR.explicitOver
    )

random(ZZ, WittPolynomialRing) := opts -> (nn, WPR) -> (
    R := WPR.unWitt;
    ll := WPR.wittLength;
    witt apply(toList(1..ll), xx -> random(nn, R))
    )


-------------------------------
-------------WittQuotientRing
-------------------------------

--TODO: make sure arithmetic of witt vectors in WittQuotientRing work fine.

WittQuotientRing = new Type of MutableHashTable;

witt(ZZ, QuotientRing) := (n,R)->(
    if not R.?cache then(
	R.cache = new CacheTable;
	);
    if not R.cache.?wittRings then(
	R.cache.wittRings = new CacheTable;
	);
    if not R.cache.wittRings#?n then(
	W := new WittQuotientRing from MutableHashTable;
	W.wittLength = n;
	W.unWitt = R;
	W.overring = wittOverring(n,R);
	R.cache.wittRings#n = W;
	);
    R.cache.wittRings#n
)

net(WittQuotientRing) := WQR -> (
    return horizontalJoin("Witt", (net(WQR.wittLength))^-1, "(", net WQR.unWitt, ")")
    )

explicit(WittQuotientRing) := WQR->(
	if (not WQR.?explicit) then(
		WQR.explicit = wittVectors(WQR.wittLength, WQR.unWitt);
	);
	return WQR.explicit;
	)

explicitOver(WittQuotientRing) := WQR -> (
    -- make cache!
    WQR.explicitOver
    )

random(ZZ, WittQuotientRing) := opts -> (nn, WQR) -> (
    R := WQR.unWitt;
    ll := WQR.wittLength;
    witt apply(toList(1..ll), xx -> random(nn, R))
    )


-------------
------------- WittIdeal
-------------

WittIdeal = new Type of MutableHashTable;

protect wittGenerators

wittIdeal(WittRingElement) := ww -> (
    jj := new WittIdeal from {wittGenerators => toSequence{ww}};
    return jj;
    )

wittIdeal List := wittIdeal Sequence := LL -> (
    if not all(LL, ll -> class(ll) === WittRingElement) then(
	error "the suggested generators are not WittRingElement";
	);
    if not length unique apply(LL, ll -> length(ll)) == 1 then(
	error "the generators do not have the same length";
	);
    jj := new WittIdeal from {wittGenerators => toSequence(LL)};
    return jj;
  )

---

explicit(WittIdeal) := I -> (
    if not I.?explicit then(
	Igens := I.wittGenerators;
	Igensover := apply(Igens, explicit);
	I.explicit = ideal(Igensover);
	);
    I.explicit
    )

explicitOver(WittIdeal) := I -> (
    if not I.?explicitOver then(
	Igens := I.wittGenerators;
	Igensover := apply(Igens, explicitOver );
	I.explicitOver = ideal(Igensover);
	);
    I.explicitOver
    )

trim (WittIdeal) := opts -> I -> (
    Iexp := trim(explicit(I));
    ggs := apply( flatten entries gens Iexp, wittRingToTuple);
    wittIdeal(ggs)
    )

generators (WittIdeal) := opts -> I -> (
    toSequence I.wittGenerators
    )

---- containment: TODO

--- equality

WittIdeal == WittIdeal := (I, J) -> (
    explicit(I) == explicit(J)
    )

--- addition and multiplication

WittIdeal + WittIdeal := (I,J) -> (
    Igens := I.wittGenerators;
    Jgens := J.wittGenerators;
    wittIdeal(Igens | Jgens)
    )

WittIdeal * WittIdeal := (I, J) -> (
    Igens := I.wittGenerators;
    Jgens := J.wittGenerators;
    outputGens := flatten (for gg in Igens list (for xx in Jgens list( gg*xx ) ));
    wittIdeal(outputGens)
    )

--WittIdeal display

addCommas := LL -> (
    nn := #LL;
    out := ();
    for jj in 0..(2*nn-2) do(
	if jj % 2 == 0 then(
	    out = append(out, LL#(jj//2))
	    ) else (
	    out = append(out, ", ");
	    );
	);
    out
    )

net WittIdeal := WI -> (
    wgs := WI.wittGenerators;
    if #wgs == 1 then(
	return horizontalJoin("ideal ", net (wgs#0));
	) else (
	wgsnet := apply( wgs, net );
	wgsnet = addCommas(wgsnet);
	return horizontalJoin("ideal (", wgsnet, ")"  );
    );
)

------------ WittMatrix

WittMatrix = new Type of MutableHashTable;
