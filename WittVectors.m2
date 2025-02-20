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
"wittVectors",
"WittRingElement",
"wittTupleToOverring",
"wittTupleToRing",
"wittRingToTuple",
"wittOverringToTuple",
"verschiebung",
"frobeniusOnWitt",
"wittOverringIdeal",
"wittRingIdeal",
"unWitt",
"overringMap",
"WittRing",
"wittSub",
"wittOverrings",
"CropWittVector",
"WittPolynomialRing",
"explicit",
"wittRings",
"WittIdeal",
"wittIdeal",
"wittGenerators",
"tuple",
"explicitOver",
"MaxHeight",
"findFrobeniusLiftConstraints",
"findFrobeniusLift",
"createEquations",
"table2", --MAYBE
"quasiFSplittingNumber",
"fSplittingHeight",
}




load "Kernels.m2"
load "Verschiebung.m2"
load "FrobeniusWitt.m2"
load "Quotients.m2"
load "WittConstructor.m2"
load "FlatLiftings.m2"
load "QuasiFSplittings.m2"
load "tests.m2"

needsPackage "Polyhedra"
needsPackage "SLPexpressions"
needsPackage "MinimalPrimes"
rld = () -> (loadPackage "WittVectors")

---NEW TO DO
---1. 


---TO DO
---1. Debug level for addition/multiplication/etc
---2. Functoriality
---3. fix kernelZZ to be more robust (should be able to get rid of degree check in wittTupleToRing)
---4. implement test for non-defined maps
---5. in wittOverringToTuple, does going mod a smaller power of p speed things up?
---6. Prove that wittVector(n,R) is actually the ring of Witt Vectors of R.

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
--- 9. subtract witt vectors

--- 9. This should throw an error instead of looping forever: R = GF(3)[x,y]; explicit(witt{z,y})


wittOverring = method()
wittOverring(ZZ, Ring) := (n, R) -> (
    if class R =!= PolynomialRing then(
	--error "wittOverring currently only implemented for polynomial rings";
        S := ambient R; 
        --TODO: flattenRing S before checking its polynomial?
        if class S =!= PolynomialRing then( error "wittVectors currently only implemented for quotients of polynomial rings");
        I:=ideal R; 
        return quotient wittOverringIdeal(n,I)
	);
    Rvars := flatten entries vars R;
    p := char R;
    d := length Rvars;
    -- we create the WittOverring; called so because the n-th Witt ring of R
    -- will be a subring of this WittOverring.
    if not R.?cache then(
	R.cache = new CacheTable
	);
    if not R.cache.?wittOverrings then(
	R.cache.wittOverrings = new MutableHashTable;
	);
    if not R.cache.wittOverrings#?n then(
	T := symbol T;
	OR := ZZ[T_1 .. T_d] / p^n;
	OR.cache = new CacheTable;
	ORvars := flatten entries vars OR;
	WittSub := map(OR, R, ORvars); -- WARNING: this is not a "real" map!
	OR.cache.wittSub = WittSub;
	OR.cache.unWitt = R;
	R.cache.wittOverrings#n = OR;
	);
    R.cache.wittOverrings#n
)

wittTupleToOverring = method()
wittTupleToOverring(List) := (LL) -> (
    R := ring first LL;
    p := char R;
    n := length LL;
    OR := wittOverring(n, R);
    WittSub := OR.cache.wittSub;
    WittLL := apply(LL, ff -> WittSub(ff));
    
    --for j from 0 to n-1 do ( declareVariable inp_j; );
    --outp := sum (for j from 0 to n-1 list p^j*((inp_j)^(p^(n-1-j))));
    --slp = makeInterpretedSLProgram(for j from 0 to n-1 list inp_j, {outp});
    --return (evaluate(slp,matrix{WittLL}))_0_0;
    sum toList apply(0..(n-1), j -> p^j*(WittLL#j)^(p^(n-1-j)) )
    )
--ww = (xx) -> wittTupleToOverring(xx);



wittVectors=method()
wittVectors(ZZ,Ring):=(n,R)->(
    --if n == 1 then return R;
    -- check if R is polynomial ring
    if class R =!= PolynomialRing then( 
    	--error "wittVectors currently only implemented for polynomial rings";
        S := ambient R; 
        --TODO: flattenRing S before checking its polynomial?
        if class S =!= PolynomialRing then( error "wittVectors currently only implemented for quotients of polynomial rings");
        I:=ideal R; 
        return quotient wittRingIdeal(n,I)
    );
    --
    if R.?cache==true and R.cache.?WittRing==true and R.cache.WittRing#?n==true then return R.cache.WittRing#n else
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
    B:=wittOverring(n,R);
    L := for i in cubes list p^(first i)*(product for j from 0 to d - 1 list B_j^((last i)_j*p^(n-first i -1)));
    aA := ambient A;
    iA := ideal A;
    K := kernelZZ map(B, A, L);
    aK := sub(K, aA);
    WR := quotient (iA + aK);
    Phi := map(B,WR,L);
    --this is all caching stuff
    WR.cache.overringMap=Phi;
    WR.cache.unWitt = R;
    if R.?cache==false then R.cache= new CacheTable;
    if R.cache.?WittRing==false then R.cache.WittRing = new MutableHashTable ;
    (R.cache.WittRing)#n = WR;
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
    
    OR1 := wittOverring(n-1, R);
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



---
--- Eamon: note that when variables are indexed, like in R = GF(3)[x_1, x_2], wittVectors does
--- not work. I tried to implement the function addIndex below, but I am stuck...
--- The goal would be that, e.g., for R = GF(3)[x_1, x_2], the function addIndex(3, x_2)
--- would return x_(2,3). So far it works for R = GF(3)[x, y]...
---

addIndex = method() 

addIndex(ZZ, IndexedVariable) := (n, x) -> (
    inputSymbol := x#0;
    inputIndex := x#1;
    if ((class inputIndex) === ZZ) then (inputIndex = toSequence{inputIndex});
    newIndex := append(inputIndex, n);
    inputSymbol_newIndex
    )

addIndex(ZZ, Symbol) := (n, x) -> (
    x_n
    )

addIndex(ZZ, RingElement) := (n, x) -> (
    (varName, varIndex) := breakString(toString x);
    varIndex = value varIndex;
    addIndex(n, (getSymbol varName)_varIndex)   
    )
    
---

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
