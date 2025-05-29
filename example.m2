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
