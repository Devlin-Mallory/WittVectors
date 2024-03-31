needsPackage "TestIdeals"
needsPackage "WittVectors"
needsPackage "PushForward"

Delta1=method()
Delta1(RingElement):=a->(
last (wittOverringToTuple( wittTupleToOverring({a,0})-sum apply(terms a,i->wittTupleToOverring({i,0})))).tuple
)


fn=method()
fn(ZZ,RingElement):=(n,f)->(
p:=char ring f;
m:=ideal gens ring f;
if n == 1 then return f^(p-1);
  D:=Delta1(f^(p-1));
exponentList := apply(toList(0..n-2),i->D^(p^i) % frobeniusPower(p^n,m));
  De:=(product exponentList) % frobeniusPower(p^n , m);
(f^(p-1)*De) % frobeniusPower(p^n , m)
)

---fn2 returns actual value, not modulo anything
fn2=method()
fn2(ZZ,RingElement):=(n,f)->(
p:=char ring f;
if n == 1 then return f^(p-1);
D:=Delta1(f^(p-1));
if n == 2 then return f^(p-1)*D;
D^(p^(n-2))*fn2(n-1,f))

fn3=method()
fn3(ZZ,RingElement,ZZ):=(n,f,t)->(
p:=char ring f;
m:=ideal gens ring f;
if n == 1 then return f^(p-1);
D:=Delta1(f^(p-1));
if n == 2 then return f^(p-1)*(D % frobeniusPower(p^t,m));
(D^(p^(n-2)) % frobeniusPower(p^t,m))*fn3(n-1,f,t))






quasiFSplittingNumber=method()
quasiFSplittingNumber(Ideal,ZZ):=(I,max)->(
f:=product( I_*);
S:=ring I;
p:=char S;
m:=ideal gens S;
 for i from 1 to max do if not isSubset(ideal fn3(i,f,i) ,frobeniusPower(p^i,m)) then return i
)

u = method()
u(ZZ,RingElement) :=(e,f)->(
S:=ring f;
if class S =!= PolynomialRing then error "needed an element of a polynomial ring";
n:=numgens S;
p:=char S;
termsf := terms f;
--exponentsf := flatten apply(termsf, exponents);
sum apply( select(termsf, i-> ((flatten exponents i) % p^e) == toList(n:p^e-1)), i-> (last coefficients(i)  ) * S_(flatten exponents(i)//p^e))
)

theta=method()
theta(RingElement,RingElement):= (f,a) ->(
p:=char ring f;
u(1,Delta1(f^(p-1))*a)
)


fSplittingHeight=method(Options=>{MaxHeight=>100})
fSplittingHeight(Ideal) := ZZ => opts-> I0->(
S:=ring I0;
if class S =!= PolynomialRing then return "error: expected ambient ring to be a polynomial ring";
if codim(I0) < numgens I0 then return "error: expected ideal to be a complete intersection";
p:=char S;
if p == 0 then return "error: expected a ring of characteristic p";
A:=dim S-1;
ff:=product I0_*;
Frob := map(S,S,matrix{apply(gens S,u->u^p)});
(FS,GS,transformS) := pushFwd(Frob);

M := ideal (gens S);
MP := frobenius(1,M);
v := product(A+1, i -> (S_i)^(p-1));
u0:= map(S^1 ,FS,transpose(transformS(v)));


I:= ideal ff^(p-1);
if not isSubset(I,MP) then return 1;
elapsedTime if isSubset(ideal ff^(p-2),MP) then return infinity;
elapsedTime if isSubset((ideal( ff^(p-2))+frobenius(1,I0))*ff^(p*(p-2))*Delta1(ff),frobenius(2,M)) then return infinity;

del:=Delta1(ff^(p-1));
K := pushmultiple(del,GS,transformS);
II:=I;

for i from 2 to opts.MaxHeight do
(
print( "trying i = "|i);
FI := image(pushideal(I,GS,transformS));
u:=map(S^1,ambient FI,u0);
FS:= source u;
J := intersect(FI, kernel(u));
JJ := inducedMap(FS,J);
KK := image(u*K*JJ);
II := ideal(mingens KK) + ideal(ff^(p-1));
if not isSubset(II, MP) then break return i;
if I == II then break return infinity;
I=II;
);
)

pushmultiple = (r,GS,transformS)->(
A:=dim ring r - 1;
p:=char ring r;
FS:=source GS;
S:=target GS;
C:=transformS(r*GS_(0,(0)));
for j from 2 to p^(A+1) do
(
D:=transformS(r*GS_(0,(j-1)));
E:=C|D;
C=E;
);
map(FS, S^(p^(A+1)), C)
);

pushideal = (I,GS,transformS)->(
matrix{for i in I_* list pushmultiple(i,GS,transformS)}
)






table2=method()
table2(ZZ):=n->(
S=(ZZ/3)[x,y,z,w];
I:=new MutableHashTable from {};
I#1=x^4 + y^4 + z^4 + 2*w^4 + x^2* y*w + y*z^2*w;
I#2=x^4 + 2*y^4 + 2*z^4 + 2*w^4 + x*y*z^2;
I#3=x^4 + y^4 + z^4 + w^4 + x^2*z^2 + x*y*z^2 + z^3*w;
I#4=x^4 + y^4 + z^4 + w^4 + x^2*z^2 + x*y*z^2;
I#5=x^4 + y^4 + z^4 + w^4 + x^3*z + z^3*w + y*z^2*w + y*z*w^2;
I#6=x^4 + y^4 + z^4 + w^4 + x^2*z^2 + x^2*y*z;
I#7=x^4 + y^4 + z^4 + w^4 + x*y^2*z + x*z^2*w + y*z*w^2 + y^2*z*w;
I#8=x^4 + x^2*y*z + x^2*y*w + 2*x^2*z^2 + x*y*w^2 + 2*y^4 + y^3*w + z^4 + w^4;
I#9=x^4 + y^4 + z^4 + w^4 + x*y^3 + y^3*w + z^2*w^2 + 2*x*y*z^2 + y*z*w^2;
I#10=x^4 + 2*x^2*y*z + x^2*y*w + x*y^2*w + y^4 + y^3*w + y^2*z^2 +2*y^2*z*w + y^2*w^2 + y*z^3 + y*z^2*w + y*z*w^2 + z^4 + z*w^3;
I#11=x^4 + y^4 + z^4 + w^4;
if n>10 then return I#11 else return I#n
)

artinMazur60 = () -> (
S:=(ZZ/2)[x,y,z,w,u];
 x^5 + y^5 + z^5 + w^5 + u^5 + x*z^3*w + y*z*w^3 + x^2*z*u^2 + y^2*z^2*w + x*y^2*w*u + y*z*w*u^2)

sampleCY=(p,n,N)->(
x:=symbol x;
S:=(ZZ/p)[x_0..x_(n+1)];
m:=ideal gens S;
for i from 1 to N list(
print "---------";
I:=ideal (x_0^2);
while( dim radical(I+ ideal jacobian I) > 0 or isFPure(I)) do I=ideal(random(n+2,S));
print("sample number "|i);
(fSplittingHeight(I),I)
)
)




