
needsPackage "PushForward"; --compute Quasi-F-split height and I_\infty
p := 3;
A:=3; -- A+1 is the number of variables
Sup:=100;-- compute In for n \leq Sup+1
S := ZZ/p[vars{0..A}];
S = ZZ/p[x,y,z,w];
S' := ZZ[ gens S ];
--ff:=a^2+b^3+c^5; --Given equation
--ff:=c^2 + a^3 + b^2*c + a*b*c 
--ff:=x^4 + y^4 + z^4 + w^4 + x*y^2*z + x*z^2*w + y*z*w^2 + y^2*z*w;
--ff=x^4 + 2*y^4 + 2*z^4 + 2*w^4 + x*y*z^2;
ff:=x^4 + 2*x^2*y*z + x^2*y*w + x*y^2*w + y^4 + y^3*w + y^2*z^2 +2*y^2*z*w + y^2*w^2 + y*z^3 + y*z^2*w + y*z*w^2 + z^4 + z*w^3;



   　　
delta1 := (f) -> (
liftf:= sub(f, S');
liftfp:= sub(f^p, S');
(liftf^p-liftfp)//p
);

Frob := map(S,S,matrix{apply(gens S,u->u^p)});
(FS,GS,transformS) := pushFwd(Frob);

use S;
L := gens S;
M := ideal (gens S);
MP := sum(A+1, i-> ideal((L#i)^(p)));
v := product(A+1, i -> (L#i)^(p-1));
u:= map(S^1 ,FS,transpose(transformS(v)));
ffnew:=sub(ff,S);
ff:=ffnew;



--pushideal := (I) -> (
--B:= numgens I;
--C = genericMatrix(S,a,p^(A+1),0);
--for i from 1 to B do
--(
--for j from 1 to p^(A+1) do
--(
--D:=transformS((I_(i-1))*GS_(0,(j-1)));
--E:=C|D;
--C=E;
--);
--);
--map(FS, S^(B*p^(A+1)), C)
--);

pushmultiple:=(r)->(
C:=transformS(r*GS_(0,(0)));
for j from 2 to p^(A+1) do
(
D:=transformS(r*GS_(0,(j-1)));
E:=C|D;
C=E;
);
map(FS, S^(p^(A+1)), C)
);

pushideal:=(I)->(
matrix{for i in I_* list pushmultiple(i)}
)



--pushmultiple := (r) -> (
--C = genericMatrix(S,a,p^(A+1),0);
--for j from 1 to p^(A+1) do
--(
--D:=transformS(r*GS_(0,(j-1)));
--E:=C|D;
--C=E;
--);
--map(FS, S^(p^(A+1)), C)
--);

I= ideal (sub(ff^(p-1),S));

del:=sub(delta1(ff^(p-1)),S);
K := pushmultiple(del);

if not isSubset(I,MP) then (
Sup =0;
print("ht", 1)
) else
(
print(1)
)

for i from 1 to Sup do
(
FI = image(pushideal(I));
J = intersect(FI, kernel(u));
JJ = inducedMap(FS,J);
KK = image(u*K*JJ);
II = ideal(mingens KK) + ideal(ff^(p-1));
if not isSubset(II, MP) then (
if not I == II then
(
print("ht leq", i+1);
) else 
(
print ("ht leq" ,i+1, "I_infty");
break;
);
I = II;
) else
(
if not I == II then
(
print(i+1);
) else 
(
print ("ht infinity", i+1, "I infinity");
break;
);
I =II;
);
)
