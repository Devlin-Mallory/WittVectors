--here's where we'll define classes and class operations



witt = method()
wittLength = method()
explicit = method()
explicitOver = method()
wittIdeal = method(Dispatch => Thing)
verschiebung = method()

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

wittFrobenius = method()
wittFrobenius(WittRingElement) := ww -> wittFrobenius(1, ww)

wittFrobenius(ZZ, WittRingElement) := (nn,ww) -> (
    p := char (ring ww).unWitt;
    witt apply(ww.tuple, i-> i^(p^nn))
    )

verschiebung(WittRingElement) := ww -> (
    R := (ring ww).unWitt;
    witt({0_R}|ww.tuple)
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

--should this be WittRingElement?
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

protect overring
protect unWitt 

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

wittLength(WittQuotientRing) := W -> W.wittLength
wittLength(WittPolynomialRing) := W -> W.wittLength

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




----------------------------------
---------------- WittRingMap
---------------------------------

-- currently the implementation is for maps witt(n,R) -> witt(n,S) arising from maps R -> S
-- but it's less clear how to represent a general map WR -> WS

-- Do we want to allow syntax map(WittRing, WittRing, {...})?

WittRingMap = new Type of MutableHashTable;

net(WittRingMap) := Wf->(
	return horizontalJoin("WittRingMap ", net(Wf.target), " <-- ", net(Wf.source));
)

witt(ZZ, ZZ , RingMap) := WittRingMap => (mm, nn, ff) -> (
    if mm > nn then error "wittLength of target is bigger than wittLength of source";
    R := source ff;
    S := target ff;
    WR := witt(nn, R);
    WS := witt(mm, S);
    Wf := new WittRingMap from MutableHashTable;
    Wf.source = WR;
    Wf.target = WS;
    Wf.baseMap = ff;
    Wf
    )

witt(ZZ, RingMap) := WittRingMap => (n, f) -> (
    witt(n,n,f)
    )

WittRingMap * WittRingMap :=  WittRingMap => (gg, ff) -> (
    if source gg =!= target ff then error "WittRingMap's given are not composable";
    witt( target(gg).wittLength, source(ff).wittLength , ff.baseMap*gg.baseMap)
)

explicit(WittRingMap) := Wf -> (
    Wse := explicit source Wf;
    Wte := explicit target Wf;
    mapList := for i in gens Wse list wittTupleToRing( witt apply((wittRingToTuple i).tuple, j->(baseMap Wf)(j) ));
    map(Wte, Wse, mapList)
)


WittRingMap ^ ZZ := (Wf, mm) -> (
    f := baseMap(Wf);
    ll := Wf.wittLength;
    fm := f^mm;
    witt(ll, fm)
    )

target(WittRingMap) := W -> W.target
source(WittRingMap) := W -> W.source

baseMap = method()
baseMap(WittRingMap) := W -> W.baseMap

WittRingMap WittRingElement := WittRingElement => (Wf, w) -> (
    --TODO: impliement with witt(n,m,f)
    f := baseMap(Wf);
    wList := toList(w);
    outputList := apply(wList, xx -> f(xx));
    witt(outputList)
    )
