
wittVectors=method()
wittVectors(ZZ,Ring):=(n,R)->(
p:=char R;
d:=numgens R;
A:=ZZ[flatten for x in gens R list toList(x_0..x_n)];
--x_(i) is p^i * x^(1/p^i)
J:=ideal flatten for i from 0 to d-1 list (
                     for j from 0 to n-1 list( p^p*A_(i*n+j)-A_(i*n+j+1)^p)
);
VnA:=ideal(for i from 0 to d-1 list p^(n)*A_(i*(n+1)+n)   );
J+VnA+p^n
)

