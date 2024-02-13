--here's where we'll define classes and class operations

witt = method()
explicit = method()

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
    ww.tuple = apply(L0,i->sub(i, first BaseRing ));
    return ww
)

net(WittRingElement) := w -> (w.tuple)

--TODO: here I would like R = GF(3)[x]; W = witt(2, R); w = witt({x, x+1}); ring w
-- to return W instead of Witt_2(R). Tried to do it with caching below but failed. 
--
--
ring(WittRingElement) := W -> (
    R := ring(W#0); -- note that witt subs every entry into R so this is good enough
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

WittRingElement + WittRingElement := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if ring w1 =!= ring w2 then error "expected elements of the same ring";
    w1over := wittTupleToOverring w1;
    w2over := wittTupleToOverring w2;
    outputover := w1over + w2over;
    wittOverringToTuple outputover
    )

WittRingElement * WittRingElement := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if ring w1 =!= ring w2 then error "expected elements of the same ring";
    w1over := wittTupleToOverring w1;
    w2over := wittTupleToOverring w2;
    outputover := w1over * w2over;
    wittOverringToTuple outputover
    )

explicit(WittRingElement) := w -> (
    if not w.?explicit then( 
	w.explicit = wittTupleToRing(w.tuple);
	);
    w.explicit
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
	-- TODO: Make the subscript actually a subscript
	return "Witt_" | WPR.wittLength | "(" | (toString WPR.unWitt) | ")";
)

explicit(WittPolynomialRing) := WPR->(
	if (not WPR.?explicit) then(
		WPR.explicit = wittVectors(WPR.wittLength, WPR.unWitt);
	);
	return WPR.explicit;
)


-------------
-------------WittIdeal
-------------

WittIdeal = new Type of MutableHashTable;

protect wittGenerators

ideal(WittRingElement) := w -> (
    print "aaa";
    jj := new WittIdeal from {wittGenerators => "a"};
    print jj.wittGenerators;
    return jj;
    )

--net WittIdeal := WI -> (
    --return "ideal" | net(WI.wittGenerators);
    --)

------------WittMatrix

WittMatrix = new Type of MutableHashTable;

-------------WittQuotientRing

WittQuotientRing = new Type of MutableHashTable;

protect wittIdeal
protect wittAmbient

WittPolynomialRing / WittIdeal := (WPR, WI) -> (
    Q := new WittQuotientRing from MutableHashTable;
    Q.wittAmbient = WPR;
    Q.wittIdeal = WI;
    return Q
    )

net(WittQuotientRing) := QR -> (
    (expression QR.wittAmbient) / (expression QR.wittIdeal)
    )
