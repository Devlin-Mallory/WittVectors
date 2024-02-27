--here's where we'll define classes and class operations

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
    if ring w1 =!= ring w2 then error "expected elements of the same ring";
    w1over := explicitOver(w1);
    w2over := explicitOver(w2);
    outputover := w1over + w2over;
    wittOverringToTuple outputover
    )

WittRingElement * WittRingElement := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if ring w1 =!= ring w2 then error "expected elements of the same ring";
    w1over := explicitOver(w1);
    w2over := explicitOver(w2);
    outputover := w1over * w2over;
    wittOverringToTuple outputover
    )

explicit(WittRingElement) := w -> (
    if not w.?explicit then( 
	w.explicit = wittTupleToRing(w.tuple);
	);
    w.explicit
    )

explicitOver(WittRingElement) := ww -> (
    if not ww.?explicit then(
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

-------------WittPolynomialRing

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
    jj := new WittIdeal from {wittGenerators => toSequence(LL)};
    return jj;
  )

--addition

WittIdeal + WittIdeal := (I,J) -> (
    Igens := I.wittGenerators;
    Jgens := J.wittGenerators;
    wittIdeal(Igens | Jgens)
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

------------- WittQuotientRing

WittQuotientRing = new Type of MutableHashTable;

protect wittAmbient

--WittPolynomialRing / WittIdeal := (WPR, WI) -> (
  --  Q := new WittQuotientRing from MutableHashTable;
   -- Q.wittAmbient = WPR;
   -- Q.wittIdeal = WI;
   -- return Q
   -- )

--net(WittQuotientRing) := QR -> (
  --  (expression QR.wittAmbient) / (expression QR.wittIdeal)
   -- )
