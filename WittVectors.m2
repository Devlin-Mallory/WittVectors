needs "Kernels.m2"
needsPackage "Polyhedra"
rld = () -> (load "WittVectors.m2")


---
--- Eamon: here is an idea (from Karl). Maybe change the names of output variables
--- so that, e.g., the variable that corresponds to p^3 x^(2/p^3) is called
--- p3x_2, or something like that?
---

 
wittVectors=method()
wittVectors(ZZ,Ring):=(n,R)->(
--if n ==1 then return R;
-- check if R is polynomial ring
if class R =!= PolynomialRing then( 
    return "error: wittVectors currently only implemented for polynomial rings";
    );
--
p:=char R;
d:=numgens R; -- number of variables
--indxs := flatten for i from 0 to n-1 list for j from 1 to max(p^i-1,1) list (i,j);
baseVariables:=apply(for i from 0 to d-1 list insert(i,1,toList(d-1:0)),j->{0}|{j});
cubes := baseVariables| sort select( flatten for i from 1 to n-1 list apply(flatten \ entries \ latticePoints hypercube(d, 0, p^(i) - 1),j->{i}|{j}), i->last i != toList(d:0));
--A:=ZZ[flatten for x in gens R list apply(indxs,i->x_i)]/p^n;
T:=symbol T;
A:=ZZ[for i in cubes list T_i]/p^n;
t:=symbol t;
B:=ZZ[t_0..t_(d-1)]/p^n;
L:= for i in cubes list p^(first i)*(product for j from 0 to d - 1 list B_j^((last i)_j*p^(n-first i -1)));
--L:=flatten flatten for j from 0 to d-1 list for i from 0 to n-1 list for k from 1 to max(p^i-1,1) list p^i* B_j^(k*p^(n-i-1));
--x_(i) is p^i * x^(1/p^i)
--quotient kernelZZ map(B,A,L)
aA := ambient A;
iA := ideal A;
K := kernelZZ map(B, A, L);
aK := sub(K, aA);
WR:=quotient (iA + aK);
Phi:=map(B,WR,L);
WR.cache.overringMap=Phi;
if R.?WittRing==false then R.WittRing = new MutableHashTable ;
(R.WittRing)#n = WR;
--R.WittRing=WR;
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
WR := if R.?WittRing == true then (if R.WittRing#?n == true then R.WittRing#n else wittVectors(n,R)) else  wittVectors(n,R);
Phi := WR.cache.overringMap;
OR := target Phi;
use R;
 --for i from 0 to n-1 list p^i*((map(OR,R,for j from 0 to numgens R-1 list OR_j^(p^(i))))(L_i))
G:=sum for i from 0 to n-1 list p^i*((map(OR,R,for j from 0 to numgens R-1 list OR_j^(p^(i))))(L_i))^(p^(n-1-i));
print G;
sum for m in terms G list(
(B,pi):=flattenRing quotient ideal m;
--the below method doesn't always work to find a preimage... we should figure out a better way
preimages := (kernelZZ(pi*map(source pi,WR,Phi)))_*;
multiplied:=flatten for i in preimages list for j from 1 to p^n-1 list i*j;
first select(multiplied,i->Phi(i)==m)
)
--G//Phi(vars source Phi)
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
    addIndex( n, getSymbol toString x )
    )
    
---
---


