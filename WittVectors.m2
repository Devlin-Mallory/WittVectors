newPackage(
    "WittVectors",
    Version => "0.01",
    Date => "December 4, 2023",
    Authors => {
    	{Name => "Anne Fayolle", Email => "anne.fayolle@utah.edu", HomePage => "https://annefayolle.github.io/"},
	{Name => "Abhay Goel", Email => "u1421426@utah.edu", HomePage => "https://faculty.utah.edu/u1421426-ABHAY_GOEL/teaching/index.hml"},
	{Name => "Devlin Mallory", Email => "malloryd@math.utah.edu", HomePage => "https://www.math.utah.edu/~malloryd/"},
	{Name => "Eamon Quinlan-Gallego", Email => "eamon.quinlan@utah.edu", HomePage => "https://eamonqg.github.io/"},
    	{Name => "Teppei Takamatsu", Email => "teppeitakamatsu.math@gmail.com", HomePage => "https://sites.google.com/view/teppei-takamatsu/home"}
    },
    Headline => "A Macaulay2 package for Witt vectors",
    Keywords => {"Witt Vectors"},
    DebuggingMode => true,
    Reload => true,
    AuxiliaryFiles => true
    )

export{
"rld",
"witt",
"wittOverring",
--"wittVectors",
"WittRingElement",
"wittTupleToOverring",
"wittTupleToRing",
"wittRingToTuple",
"wittOverringToTuple",
"verschiebung",
"wittOverringIdeal",
"wittRingIdeal",
"unWitt",
"overringMap",
"WittRing",
"wittSub",
"wittOverrings",
"CropWittVector",
"WittPolynomialRing",
"WittRingMap",
"baseMap",
"WittQuotientRing",
"explicit",
"wittLength",
"wittRings",
"WittIdeal",
"wittIdeal",
"wittGenerators",
"tuple",
"explicitOver",
"MaxHeight",
"Nontrivial",
"findFrobeniusLiftConstraints",
"findFrobeniusLift",
"createEquations",
"table2", --MAYBE
"quasiFSplittingNumber",
"fSplittingHeight",
"overring",
"wittFrobenius"
}




needsPackage "TestIdeals"
needsPackage "Polyhedra"
needsPackage "PushForward"
needsPackage "SLPexpressions"
needsPackage "MinimalPrimes"
needsPackage "Elimination"
rld = () -> (loadPackage "WittVectors")

load "WittConstructor.m2"
load "Kernels.m2"
load "Verschiebung.m2"
load "Quotients.m2"
load "FlatLiftings.m2"
load "QuasiFSplittings.m2"
load "tests.m2"



---NEW TO DO
---1. witt of ring map (DONE) and have it act on elements
---2. once we have Verschiebung and frobenius for overring elements, delete the m2 files defining them
---3. move all package imports to this file
---4. change all wittTupleTo(Over)ring(List) to WittRingElement version
---5. decide about explicit witt ring class
---7. method for WR -> R? (currently available as WR.unWitt) likewise wittLength


---TO DO
---1. Debug level for addition/multiplication/etc
---2. Functoriality
---3. fix kernelZZ to be more robust (should be able to get rid of degree check in wittTupleToRing)
---4. implement test for non-defined maps
---5. in wittOverringToTuple, does going mod a smaller power of p speed things up?

---7. New classes: WittVector(call this WittElement?), WittRing, WittIdeal, WittMap(?).
--- Put these in WittConstructor
--- All these should have .element, .ring, etc... to get the gross representations.
--- Change names of current methods to address this.
--- Implement methods for WittElement, WittRing, WittIdeal, WittMap, etc...

--- Classes to be implemented:
--- WittPolynomialRing (done)
--- WittQuotientRing
--- WittRingElement -- evaluate on a polynomial
--- WittRingMap
--- WittIdeal (ideal) -- exponentiation, generators, numgens, 
--- WittMatrix
--- WittModule
---
--- All custom keys should go in the constructor of the custom class.

--- Methods to implement: (only involve the witt ring if necessary; overring is easier)
--- ring
--- map
--- kernel (??), cokernel
--- operations on ideals
--- quotients of rings
--- trim
--- gens
--- 

--- Possible new directions: compute pushout of modules from queasi-F-split. 
--- Test for quasi-F-split for non complete intersections?
--- Frobenius lifts (rings are themselves over W_n).

--- 8. Implement for all finite fields (not just F_p for prime p)



wittOverring = method()

wittOverring(ZZ, Ring) := (n, R) -> (
    --TODO: for a quotient ring R, test wittSub of its overring.
    if class R =!= PolynomialRing then(
        S := ambient R; 
        --TODO: flattenRing S before checking its polynomial?
        if class S =!= PolynomialRing then(
	    error "wittVectors currently only implemented for quotients of polynomial rings"
	    );
        I:=ideal R;
	OR := quotient wittOverringIdeal(n, I);
	OR.cache = new CacheTable;
	ORvars := flatten entries vars OR;
	WittSub := map (OR, R, ORvars); -- WARNING: not a real map!
	OR.cache.wittSub = WittSub;
        OR.cache.unWitt = R;);
    if class R === PolynomialRing then(
        Rvars := flatten entries vars R;
        p := char R;
        d := length Rvars;
        -- we create the WittOverring; called so because the n-th Witt ring of R
        -- will be a subring of this WittOverring.
        T := symbol T;
	OR = ZZ[T_1 .. T_d] / p^n;
	OR.cache = new CacheTable;
	ORvars = flatten entries vars OR;
	WittSub = map(OR, R, ORvars); -- WARNING: this is not a "real" map!
	OR.cache.wittSub = WittSub;
	OR.cache.unWitt = R;);
    OR
)

wittTupleToOverring = method()
wittTupleToOverring(List) := (LL) -> (
    R := ring first LL;
    p := char R;
    n := length LL;
    W := witt(n, R);
    --OR := wittOverring(n, R);
    OR := W.overring;
    WittSub := OR.cache.wittSub;
    WittLL := apply(LL, ff -> WittSub(ff));
    sum toList apply(0..(n-1), j -> p^j*(WittLL#j)^(p^(n-1-j)) )
    )

wittTupleToOverring(WittRingElement) := w -> (
    W := ring w;
    R := W.unWitt;
    n := W.wittLength;
    p := char R;
    OR := W.overring;
    WittSub := OR.cache.wittSub;
    WittLL := apply(w.tuple, ff -> WittSub(ff));
    sum toList apply(0..(n-1), j -> p^j*(WittLL#j)^(p^(n-1-j)) )
    )





--calculates the explicit Witt ring of a polynomial ring
wittVectors=method()
wittVectors(ZZ,Ring):=(n,R)->(
    --if n == 1 then return R;
    --check if R is polynomial ring
    if class R =!= PolynomialRing then( 
        S := ambient R; 
        --TODO: flattenRing S before checking its polynomial?
        if class S =!= PolynomialRing then( error "wittVectors currently only implemented for quotients of polynomial rings");
        I:=ideal R; 
        return quotient wittRingIdeal(n,I)
    );
    --
    p := char R;
    d := numgens R; -- number of variables
    baseVariables := apply(for i from 0 to d-1 list insert(i,1,toList(d-1:0)),j->{0}|{j});
    -- cubes is the list of indices; 
    -- T_{n,{a_1..a_d}} corresponds to p^n * x_1^{a_1/p^n}..x_d^{a_n/p^n}
    cubes := baseVariables| sort select( flatten for i from 1 to n-1 list apply(flatten \ entries \ latticePoints hypercube(d, 0, p^(i) - 1),j->{i}|{j}), i->last i != toList(d:0));
    T := symbol T;
    A := ZZ[for i in cubes list T_i]/p^n;
    t := symbol t;
    --t_i is x_i^(1/p^n)
    --B := ZZ[t_0..t_(d-1)]/p^n;
    wittR := witt(n,R);
    B:=wittR.overring;
    L := for i in cubes list p^(first i)*(product for j from 0 to d - 1 list B_j^((last i)_j*p^(n-first i -1)));
    aA := ambient A;
    iA := ideal A;
    K := kernelZZ map(B, A, L);
    aK := sub(K, aA);
    WR := quotient (iA + aK);
    Phi := map(B,WR,L);
    --cache overringMap and unWitt
    WR.cache.overringMap=Phi;
    WR.cache.unWitt = R;
    WR
    )

wittVectors(ZZ,RingMap) := (n,f)->(
(WT,WS):=(wittVectors(n,target f),wittVectors(n, source f));
L:= for i in gens WS list wittTupleToRing(f \ (wittRingToTuple(i)));
map(WT,WS,L)
)


wittTupleToRing = method()
wittTupleToRing(List):=(L)->(
    if length unique apply(L,i->ring i) > 1 then return "error: all elements of tuple must live in the same ring";
    --if length L !=n then return "error: input tuple must be of length n";
    n:=length L;
    --if n == 1 then return first L;
    R := ring first L;
    p:=char R;
    WR := if R.?WittRing == true then (if R.WittRing#?n == true then R.WittRing#n else wittVectors(n,R)) else  wittVectors(n,R);
    --Phi := WR.cache.overringMap;
    --OR := target Phi;
    use R;
    --G takes the tuple to its image in the overring
    --G:=sum for i from 0 to n-1 list p^i*((map(OR,R,for j from 0 to numgens R-1 list OR_j^(1)))(L_i))^(p^(n-1-i));
    G:=wittTupleToOverring(L);
    Phi := (((ring G).cache.unWitt).cache.WittRing#n).cache.overringMap;
    --print G;
    sum for m in terms G list(
	if degree m == {0} then sub(m,source Phi) else(
	    (B,pi):=flattenRing quotient ideal m;
	    --the below method doesn't always work to find a preimage... we should figure out a better way    
	    preimages := (kernelZZ(pi*map(source pi,WR,Phi)))_*;
	    multiplied:=flatten for i in preimages list for j from 1 to p^n-1 list i*j;
	    first select(multiplied,i->Phi(i)==m)
	    )    
	)
    --G//Phi(vars source Phi)
    )

wittTupleToRing(WittRingElement):= w-> (
    W := ring w;
    n := W.wittLength;
    --if n == 1 then return first L;
    L := w.tuple;
    R := W.unWitt;
    p := char R;
    WR := explicit W;
    use R;
    G:=wittTupleToOverring(w);
    Phi := WR.cache.overringMap;
    --print G;
    sum for m in terms G list(
	if degree m == {0} then sub(m,source Phi) else(
	    (B,pi):=flattenRing quotient ideal m;
	    --the below method doesn't always work to find a preimage... we should figure out a better way    
	    preimages := (kernelZZ(pi*map(source pi,WR,Phi)))_*;
	    multiplied:=flatten for i in preimages list for j from 1 to p^n-1 list i*j;
	    first select(multiplied,i->Phi(i)==m)
	    )    
	)
    --G//Phi(vars source Phi)
    )




wittRingToTuple=method()
wittRingToTuple(RingElement):=(F)->(
    WR:=ring F;
    Phi:=WR.cache.overringMap;
    return wittOverringToTuple(Phi(F))
)

wittOverringToTuple = method()

wittOverringToTuple(RingElement) := F -> (
    takeRoot := (f, n) -> (
    --- in a ring of char p , takes the (1/p^n) root of a polynomial f
    R := ring f;
    p := char R;
    d := numgens R;
    yy := symbol yy;
    RY := R[yy_0 .. yy_(d-1)] / ideal( for i from 0 to d-1 list yy_i^(p^n) - R_i );
    Rsub := map( RY, R, toList( yy_0..yy_(d-1)) );
    sub(Rsub(f), R)
    );

    OR := ring F;
    R := OR.cache.unWitt;
    unWittSub := map(R, OR, vars R);
    wittSub := OR.cache.wittSub;
    (p, n) := toSequence (factor(char OR))#0;
    
    if n == 1 then(
	return witt{ unWittSub(F) });
    WR1 := witt(n-1, R); 
    OR1 := WR1.overring;
    wittReduce := map( OR1, OR, vars OR1);
    
    F0 := F % ideal(sub(p, OR));
    f0 := takeRoot( unWittSub(F0), n-1 );
    
    nextF := wittReduce( ( F - (wittSub f0)^(p^(n-1)) ) // p);
    witt{f0} | wittOverringToTuple( nextF )
    )

wittRingToTuple(Ideal) := I -> (
    Igens := flatten entries gens I;
    wittgens := apply(Igens, wittRingToTuple);
    wittIdeal(wittgens)
    )

breakString = method()
breakString(String) := s -> (
    usLocation := select(length s - 1, i -> s_i == "_");
    if length usLocation > 1 then(return "error: two underscores in string");
    usLocation = first usLocation;
    (substring(s, 0, usLocation), substring(s, usLocation + 1, length s - 1))
	)

timingTest = () -> (
    x := symbol x;
    y := symbol y;
    R := GF(7)[x,y];
for n from 1 to 5 do(
    elapsedTime wittTupleToOverring( for i from 0 to n-1 list random(3, R));
);
);    

end -- loading stops here

---
--- TESTS
---

R = GF(5)[x,y,z]
for xx in 0..0 do(
    f1 = random(3, R);
    f2 = random(2, R);
    f3 = random(4, R);
    
    tt = {f1, f2, f3};
    if not elapsedTime ( (tt == wittOverringToTuple wittTupleToOverring tt) ) then(
	print "NOOOOOOO!!!!!!";
	print tt;
	);
    )

R = GF(7)[x,y]
for n from 1 to 5 do(
    print "-----";
    print n;
    elapsedTime wittTupleToOverring( for i from 0 to n-1 list random(3, R));
)
    
---
--- GARBAGE:
---

R = GF(3)[x,y]

p = char R;
d = numgens R; -- number of variables
baseVariables = apply(for i from 0 to d-1 list insert(i,1,toList(d-1:0)),j->{0}|{j})
--cubes is the list of indices; 
--T_{n,{a_1..a_d}} corresponds to p^n * x_1^{a_1/p^n}..x_d^{a_n/p^n}

cubes = baseVariables| 
sort select( 
    flatten for i from 1 to n-1 list apply(
	flatten \ entries \ latticePoints 
	hypercube(d, 0, p^(i) - 1),j->{i}|{j}), i->last i != toList(d:0)
    );

cubes = baseVariables| sort select( flatten for i from 1 to n-1 list apply(flatten \ entries \ latticePoints hypercube(d, 0, p^(i) - 1),j->{i}|{j}), i->last i != toList(d:0));
T:=symbol T;
A:=ZZ[for i in cubes list T_i]/p^n;
t:=symbol t;
--t_i is x_i^(1/p^n)
B:=ZZ[t_0..t_(d-1)]/p^n;
L:= for i in cubes list p^(first i)*(product for j from 0 to d - 1 list B_j^((last i)_j*p^(n-first i -1)));
aA := ambient A;
iA := ideal A;
K := kernelZZ map(B, A, L);
aK := sub(K, aA);
WR:=quotient (iA + aK);
Phi:=map(B,WR,L);
--this is all caching stuff
WR.cache.overringMap=Phi;
if R.?WittRing==false then R.WittRing = new MutableHashTable ;
(R.WittRing)#n = WR;
--R.WittRing=WR;
WR
)

beginDocumentation()
load "Documentation.m2"
