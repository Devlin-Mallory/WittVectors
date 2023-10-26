needs "Kernels.m2"
rld = () -> (load "WittVectors.m2")

wittVectors=method()
wittVectors(ZZ,Ring):=(n,R)->(
-- check if R is polynomial ring
if class R =!= PolynomialRing then( 
    return "error: wittVectors currently only implemented for polynomial rings";
    );
--
p:=char R;
d:=numgens R; -- number of variables
indices := flatten for i from 0 to n-1 list for j from 1 to max(p^i-1,1) list (i,j);
 A:=ZZ[flatten for x in gens R list apply(indices,i->x_i)]/p^n;
--A:=ZZ[flatten for x in gens R list toList(x_(0)..x_(n-1))]/p^n;
t:=symbol t;
B:=ZZ[t_0..t_(d-1)]/p^n;
L:=flatten flatten for j from 0 to d-1 list for i from 0 to n-1 list for k from 1 to max(p^i-1,1) list p^i* B_j^(k*p^(n-i-1));
--x_(i) is p^i * x^(1/p^i)
quotient kernelZZ map(B,A,L)
)


wittTupleToRing = method()
wittTupleToRing(ZZ,List):=(n,L)->(
if length unique apply(L,i->ring i) > 1 then return "error: all elements of tuple must live in the same ring";
if length L !=n then return "error: input tuple must be of length n";
R := ring first L;
WR :=wittVectors(n,R);

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


