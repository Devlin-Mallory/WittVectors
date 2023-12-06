--here's where we'll define classes and class operations

WittVector = new Type of List;

witt=method()
witt(List) := L0->(
L:=apply(L0,i->ring i);
if  BaseRing= length unique select(L,i-> i =!= ZZ) > 1 then error "expected elements from the same ring";
W:=new WittVector from L0;
W.Ring = first BaseRing;
)
