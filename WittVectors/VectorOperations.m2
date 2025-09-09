
wittSum = method()
wittSum(List,List) := (a,b) -> (
	N := length a;
	R := ZZ[x_0..x_N,y_0..y_N];
	p := (factor char ring a_0)#0#0;
	return {N,R,p};
)


end

p = 5
N = 2
R = ZZ[x_0..x_N,y_0..y_N]

print("Calculating A_n for n = 0.." | (toString N));
time(
for n from 0 to N do (
	add_n = 0;
	for i from 0 to (n-1) do (
		e = p^(n-i);
		add_n = add_n + (p^i)*(x_i^e + y_i^e - add_i^e);
	);
	add_n = add_n//(p^n);
	add_n = add_n + x_n + y_n;
);
)

print("The polynomial A_" | (toString N) | " has " | (toString (#(terms add_N))) | " terms.")

print("Calculating the sum of two vectors over F_" | (toString p));
time(
K = GF(p);
print("(1, 0, 0, 0, 0, ...) + (1, 0, 0, 0, 0, ...)=");
L = toList splice(1,N:0);
phi = map(K, R, L | L);
print(apply(0..N,i -> phi(add_i)) | (1:"..."));
)

print("Calculating M_n for n = 0.." | (toString N));
time(
for n from 0 to N do (
	u = 0;
	v = 0;
	c = 1;
	e = p^n;
	for i from 0 to n do (
		u = u + c*x_i^e;
		v = v + c*x_i^e;
		c = c*p;
		e = e//p;
	);
	mul_n = u*v;
	for i from 0 to (n-1) do (
		mul_n = mul_n - mul_i;
	);
	mul_n = mul_n//p^n;
);
)

print("The polynomial M_" | (toString N) | " has " | (toString (#(terms mul_N))) | " terms.")

print("Calculating the product of two vectors over F_" | (toString p));
time(
K = GF(p);
print("(1, 1, 0, 0, 0, ...) * (1, 1, 0, 0, 0, ...)=");
L = toList splice(1,1,(N-1):0);
phi = map(K, R, L | L);
print(apply(0..N,i -> phi(mul_i)) | (1:"..."));
)
