needs "Kernels.m2"
wittVectors=method()
wittVectors(ZZ,Ring):=(n,R)->(
p:=char R;
d:=numgens R;
A:=ZZ[flatten for x in gens R list toList(x_0..x_(n-1))]/p^n;
t:=symbol t;
B:=ZZ[t_0..t_(d-1)]/p^n;
L:=flatten for j from 0 to d-1 list for i from 0 to n-1 list p^i* B_j^(p^(n-i));
--x_(i) is p^i * x^(1/p^i)
quotient kernelZZ map(B,A,L)
)


