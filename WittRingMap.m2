-- currently the implementation is for maps witt(n,R) -> witt(n,S) arising from maps R -> S
-- we could at least expand also to the truncation maps witt(n,R) -> witt(m, R) for m < n
-- but it's less clear how to represent a general map WR -> WS

-- Here is one thing we could do: given a map f: R --> S, type witt((m,n), f) with m<=n to get the induced
-- map Wf: W_n(R) --> W_m(S), which results from the composition W_n(R) --> W_n(S) --> W_m(S),
-- where the last map is truncation. Would still like to keep syntax witt(n, f) = witt((n,n), f).
-- This would allow truncation maps to also be considered WittRingMaps.

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
