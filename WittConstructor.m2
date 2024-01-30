--here's where we'll define classes and class operations

witt = method()
explicit = method()

---
--- WittRingElement
---


WittRingElement = new Type of List;


witt(List) := L0->(
L:=apply(L0,i->ring i);
BaseRing:= unique select(L,i-> i =!= ZZ);
if  length (BaseRing) > 1 then error "expected elements from the same ring";
return new WittElement from apply(L0,i->sub(i, first BaseRing ));
)

ring(WittRingElement) := W->(
ring first W
)

---
--- OPERATIONS
---

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

--ring(WittRingElement) := w -> (
--	witt(length w, ring (w#0))
--)

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
	W := new WittPolynomialRing from MutableHashTable;
	W.wittLength = n;
	W.unWitt = R;
	W.overring = wittOverring(n,R);
	W
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

-------------WittIdeal

WittIdeal = new Type of MutableHashTable;

witt(Ideal) := I->(
)
