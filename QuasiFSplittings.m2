needsPackage "TestIdeals"
needsPackage "WittVectors"

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



-------TODO: add "dummy variable" calculations to find possible lifts of frobenius; for example, take k[x,y,c,d], calculate f({x,c},{y,d}) and set equal to 0. for example, when S=(ZZ/2)[x,y,c,d] and I = x^2+y^3, we get c arbitrary and d= y^2
