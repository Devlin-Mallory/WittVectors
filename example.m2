loadPackage("WittVectors")
S = (ZZ/5)[x,y,z]
gg = random(4, S)
R = S / gg
I=ideal gg
n=3
witt(n,R)

S125=ZZ/125[x,y,z]
SZZ=ZZ[x,y,z]
gg = random(4, SZZ)
gg' = sub(gg,S125)
gg''= gg%5;
elapsedTime gg''^25;
elapsedTime gg^125;
elapsedTime sub(gg^25,S125);
elapsedTime (sub(sub(gg^5,S125), SZZ))^5;

--------
--------

R = GF(9, Variable => b)[x,y]

F = baseRing(R)
isField(F)

Fquot = ambient(F)

describe Fquot

(vars(Fquot))_(0,0)

monoid R

flattenRing (Fquot[z])

---
R = GF(9)[x,y,z] / ideal(x^2 + y^3)

S = ambient R
S' = makeBaseFieldPrime(S)
varsS' = first entries vars S'
fieldVar = varsS'_(-1)

Rvars = first entries vars R
Rvars2 = append(Rvars, fieldVar_R)

phi = map(R, S', Rvars2)

S' / kernel(phi)
