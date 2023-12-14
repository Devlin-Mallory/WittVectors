--here's where we'll define classes and class operations

WittVector = new Type of List;

witt = method()
witt(List) := L0->(
L:=apply(L0,i->ring i);
BaseRing:= unique select(L,i-> i =!= ZZ);
if  length (BaseRing) > 1 then error "expected elements from the same ring";
W:=new WittVector from apply(L0,i->sub(i, first BaseRing ));
W
)

ring(WittVector) := W->(
ring first W
)

---
--- OPERATIONS
---

WittVector + WittVector := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if ring w1 =!= ring w2 then error "expected elements of the same ring";
    w1over := wittTupleToOverring w1;
    w2over := wittTupleToOverring w2;
    outputover := w1over + w2over;
    wittOverringToTuple outputover
    )

WittVector * WittVector := (w1, w2) -> (
    if length w1 != length w2 then error "expected vectors of the same length";
    if ring w1 =!= ring w2 then error "expected elements of the same ring";
    w1over := wittTupleToOverring w1;
    w2over := wittTupleToOverring w2;
    outputover := w1over * w2over;
    wittOverringToTuple outputover
    )
