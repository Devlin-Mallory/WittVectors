
wittVectors=method()
wittVectors(ZZ,Ring):=(n,R)->(
p:=char R;
d:=numgens R;
A:=ZZ[flatten for x in gens R list toList(x_0..x_n)];
--x_(i) is p^i * x^(1/p_i)
J:=ideal flatten for i from 0 to d-2 list (
                     for j from 0 to n-1 list( p*A_(i*d+j)-A_(i*d+j+1)^p)
);
VnA:=ideal(for i from 0 to d-1 list p^(n)*A_(i*(n+1)+n)   );
VnA+J
)

