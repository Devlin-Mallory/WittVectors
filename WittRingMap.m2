-- currently the implementation is for maps witt(n,R) -> witt(n,S) arising from maps R -> S
-- we could at least expand also to the truncation maps witt(n,R) -> witt(m, R) for m < n
-- but it's less clear how to represent a general map WR -> WS

-- Here is one thing we could do: given a map f: R --> S, type witt((m,n), f) with m<=n to get the induced
-- map Wf: W_n(R) --> W_m(S), which results from the composition W_n(R) --> W_n(S) --> W_m(S),
-- where the last map is truncation. Would still like to keep syntax witt(n, f) = witt((n,n), f).
-- This would allow truncation maps to also be considered WittRingMaps.

WittRingMap = new Type of MutableHashTable;

net(WittRingMap) := Wf->(
	return horizontalJoin("WittRingMap ", net(Wf.target), " <-- ", net(Wf.source));
)

witt(ZZ, RingMap) := WittRingMap => (n, f) -> (
    R := source f;
    S := target f;
    WR := witt(n,R);
    WS := witt(n,S);
    Wf := new WittRingMap from MutableHashTable;
    Wf.source = WR;
    Wf.target = WS;
    Wf.baseMap = f;
    Wf.wittLength = n;
    Wf
)

WittRingMap * WittRingMap :=  WittRingMap => (f,g) -> (
    if source g =!= target f then error "ring maps not composable";
    witt(f.wittLength, f.baseMap*g.baseMap)
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
    f := baseMap(Wf);
    wList := toList(w);
    outputList := apply(wList, xx -> f(xx));
    witt(outputList)
    )
