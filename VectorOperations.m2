
p = 5
N = 3
A = ZZ[x_0..x_N,y_0..y_N]

print("Calculating S_n for n = 0.." | (toString N));
time(
for n from 0 to N do (
	s_n = 0;
	for i from 0 to (n-1) do (
		e = p^(n-i);
		s_n = s_n + (p^i)*(x_i^e + y_i^e - s_i^e);
	);
	s_n = s_n//(p^n);
	s_n = s_n + x_n + y_n;
);
)

print("The polynomial s_" | (toString N) | " has " | (toString (#(terms s_N))) | " terms.")

print("Calculating the sum of two vectors over F_" | (toString p));
time(
R = GF(p);
print("(1, 0, 0, 0, 0, ...) + (1, 0, 0, 0, 0, ...)=");
L = toList splice(1,N:0);
phi = map(R, A, L | L);
print(apply(0..N,i -> phi(s_i)) | (1:"..."));
)
