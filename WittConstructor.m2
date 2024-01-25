--here's where we'll define classes and class operations

WittElement = new Type of List;

witt = method()
witt(List) := L0->(
L:=apply(L0,i->ring i);
BaseRing:= unique select(L,i-> i =!= ZZ);
if  length (BaseRing) > 1 then error "expected elements from the same ring";
return new WittElement from apply(L0,i->sub(i, first BaseRing ));
)

ring(WittElement) := W->(
ring first W
)

---
--- OPERATIONS
---

WittElement + WittElement := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if ring w1 =!= ring w2 then error "expected elements of the same ring";
    w1over := wittTupleToOverring w1;
    w2over := wittTupleToOverring w2;
    outputover := w1over + w2over;
    wittOverringToTuple outputover
    )

WittElement * WittElement := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if ring w1 =!= ring w2 then error "expected elements of the same ring";
    w1over := wittTupleToOverring w1;
    w2over := wittTupleToOverring w2;
    outputover := w1over * w2over;
    wittOverringToTuple outputover
    )

-- Crop Witt vector to have a given length. We want that because that will allow us to add/multiply Witt vectors of different lengths by cropping the longer one.

CropWittVector = method ()
CropWittVector(WittElement,ZZ):= (w,n)->(
    if length w<n then error "Can't crop to something longer";
    L:={};
    for i from 0 to n-1 do {
        L_i:=w_i;-- there is an issue here with lists being unmutable
    };
    return witt L;
)

