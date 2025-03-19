--currently the implementation is for maps witt(n,R) -> witt(n,S) arising from maps R -> S
--we could at least expand also to the truncation maps witt(n,R) -> witt(m, R) for m < n
--but it's less clear how to represent a general map WR -> WS


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

--todo: add ^

target(WittRingMap) := W -> W.target
source(WittRingMap) := W -> W.source

baseMap = method()
baseMap(WittRingMap) := W -> W.baseMap
