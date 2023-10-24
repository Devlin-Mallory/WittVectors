needs "Kernels.m2"
wittVectors=method()
wittVectors(ZZ,Ring):=(n,R)->(
p:=char R;
d:=numgens R;
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

