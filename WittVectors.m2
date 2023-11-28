needs "Kernels.m2"
needs "Verschiebung.m2"
needs "Frobenius.m2"
needsPackage "Polyhedra"
rld = () -> (load "WittVectors.m2")

---TO DO
---1. Need a method from going from elements of the output of 
--    wittVectors to wittTuples
---2. Quotients of polynomial rings
---3. Frobenius map on wittVectors
---4. implement Verschiebung? 
---5. fix kernelZZ to be more robust (should be able to get rid of degree check in wittTupleToRing)
---6. implement test for non-defined maps


wittOverring = method()
wittOverring(ZZ, Ring) := (n, R) -> (
    if class R =!= PolynomialRing then(
	error "wittOverring currently only implemented for polynomial rings";
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
    
    sum toList apply(0..(n-1), j -> p^j*(WittLL#j)^(p^(n-1-j)) )
    )
--ww = (xx) -> wittTupleToOverring(xx);

wittVectors=method()
wittVectors(ZZ,Ring):=(n,R)->(
    --if n == 1 then return R;
    -- check if R is polynomial ring
    if class R =!= PolynomialRing then( 
    	error "wittVectors currently only implemented for polynomial rings";
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


wittTupleToRing = method()
wittTupleToRing(List):=(L)->(
    if length unique apply(L,i->ring i) > 1 then return "error: all elements of tuple must live in the same ring";
    --if length L !=n then return "error: input tuple must be of length n";
    n:=length L;
    --if n == 1 then return first L;
    R := ring first L;
    p:=char R;
    WR = if R.?WittRing == true then (if R.WittRing#?n == true then R.WittRing#n else wittVectors(n,R)) else  wittVectors(n,R);
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
Phi=WR.cache.overringMap;
return wittOverringToTuple(Phi(F))
)

wittOverringToTuple = method()
wittOverringToTuple(RingElement):=(F)->(
f:=F;
    OR := ring f;
    R := OR.cache.unWitt;
    d := numgens R;
    p := (radical ideal char OR)_0;
    --n := (log_p(char OR))^ZZ; 
    --the above line succeeds/fails very randomly: it works for p=5 and e=2, 4, and 5, but not 3 and 6
    n := floor(log_p(char OR));
    y:=symbol y;
    RY := R[y_0..y_(d-1)]/ideal(for i from 0 to d-1 list y_i^(p^(n-1))-R_i);
    -- This is not a real ring map!
    answer := {};
    for e from 0 to n-1 do (
        phi := map(RY, OR, for i from 0 to d-1 list y_i^(p^e));
        g := f%p;
        g0 := sub(phi(g),R);
        answer = answer | {g0};
        --f = f - wittTupleToOverring(toList (e:0_R) | {g0} | toList (n-e-1:0_R));
        --the above line was giving the wrong answer for n > 2, while the below line seems to work
         f = F - wittTupleToOverring(answer|toList(n-e-1:0_R));
        f = f//p^(e+1);
    );
    return answer;
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
    

end -- loading stops here

    
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

