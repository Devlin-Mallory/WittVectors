needsPackage "WittVectors"
needsPackage "Polyhedra"
--TODO: add methods to check flatness of families over W(n,k), and to find liftings to these rings

--TODO: add "dummy variable" calculations to find possible lifts of frobenius; for example, take k[x,y,c,d], calculate f({x,c},{y,d}) and set equal to 0. for example, when S=(ZZ/2)[x,y,c,d] and I = x^2+y^3, we get c arbitrary and d= y^2

--TODO: try to write down equations for Raynaud's example

--isFlatLift



--isFrobeniusLift = method()



findFrobeniusLift=method()
findFrobeniusLift(RingElement,ZZ) := (f,d) ->(
I:=ideal f;
S:=ring I;
n:=numgens S;
J := findFrobeniusLiftConstraints(f);
T := ring J;
L :=toList((n):0);
while (evalMap(L,I,T))(J) != 0 do (L=for i from 0 to n-1 list sum for i from 0 to d list random(i,S) );
L
)

findFrobeniusLiftConstraints=method()
findFrobeniusLiftConstraints(RingElement) := (f) ->(
S:=ring f;
d:=numgens S;
T:=prune(S[aa_0..aa_(d-1)]);
Cf:=flatten entries first coefficients f;
trim ideal (sum for i in exponents f list product for j from 0 to d-1 list (witt{T_(d+j),T_j})^(i_j)).tuple
)

findFrobeniusLiftConstraints=method()
findFrobeniusLiftConstraints(RingElement) := (f) ->(
S:=ring f;
d:=numgens S;
T:=prune(S[aa_0..aa_(d-1)]);
--Cf:=flatten entries first coefficients f;
--Ef :=flatten( exponents\ flatten entries first coefficients f) ;
--WCf:=(apply(Ef,i->product for j from 0 to d-1 list (witt{T_(d+j),T_j})^(i_j)));
--sum flatten (for i from 0 to length Cf - 1 list WCf_i*Ef_i)
l:=length exponents f;
trim ideal (sum for i from 0 to l-1 list (flatten entries last coefficients f)_i product for j from 0 to d-1 list (witt{T_(d+j),T_j})^(exponents(i)_j)).tuple
)


--TODO: add methods to check flatness of families over W(n,k), and to find liftings to these rings

--TODO: add "dummy variable" calculations to find possible lifts of frobenius; for example, take k[x,y,c,d], calculate f({x,c},{y,d}) and set equal to 0. for example, when S=(ZZ/2)[x,y,c,d] and I = x^2+y^3, we get c arbitrary and d= y^2

--TODO: try to write down equations for Raynaud's example

--isFlatLift



--isFrobeniusLift = method()



findFrobeniusLift=method()
findFrobeniusLift(RingElement,ZZ) := (f,d) ->(
I:=ideal f;
S:=ring I;
n:=numgens S;
J := findFrobeniusLiftConstraints(f);
T := ring J;
L :=toList((n):0);
while (evalMap(L,I,T))(J) != 0 do (L=for i from 0 to n-1 list sum for i from 0 to d list random(i,S) );
L
)

findFrobeniusLiftConstraints=method()
findFrobeniusLiftConstraints(RingElement) := (f) ->(
S:=ring f;
d:=numgens S;
T:=prune(S[aa_0..aa_(d-1)]);
Cf:=flatten entries first coefficients f;
trim ideal (sum for i in exponents f list product for j from 0 to d-1 list (witt{T_(d+j),T_j})^(i_j)).tuple
)

findFrobeniusLiftConstraints=method()
findFrobeniusLiftConstraints(RingElement) := (f) ->(
S:=ring f;
d:=numgens S;
T:=prune(S[aa_0..aa_(d-1)]);
--Cf:=flatten entries first coefficients f;
--Ef :=flatten( exponents\ flatten entries first coefficients f) ;
--WCf:=(apply(Ef,i->product for j from 0 to d-1 list (witt{T_(d+j),T_j})^(i_j)));
--sum flatten (for i from 0 to length Cf - 1 list WCf_i*Ef_i)
trim ideal (sum for i in exponents f list product for j from 0 to d-1 list (witt{T_(d+j),T_j})^(i_j)).tuple
)


expandFrobeniusConstraints=method()
expandFrobeniusConstraints(RingElement,ZZ) := (f,d)->(
S := ring f;
I := findFrobeniusLiftConstraints(f);
A := ring I;
n := dim ring f;
c := symbol c;
B := S[c_(toList(n:0),{1})..c_(toList(n:d),{n})];
monomials := apply(select( latticePoints hypercube(n, 0, d),i->sum entries i <= {d}),j->entries j) ;
mapList := for i from 1 to n list sum apply(monomials,j->S_(flatten j)*c_(toSequence({flatten j}|{{i}})));
expand:=map(B,A,mapList|gens S);
expand I
)

createEquations = method()
createEquations(RingElement,ZZ):=(f,d)->(
G:=expandFrobeniusConstraints(f,d);
n:=dim ring f;
S:=ring f;
p:=char S;
T:=ring G;
cc:=symbol cc;
Bcc := T[cc_(toList(n:0))..cc_(toList(n:d))];
monomials := apply(select( latticePoints hypercube(n, 0, d),i->sum entries i <= {d}),j->entries j) ;
genericElement:=sum apply(monomials,j->S_(flatten j)*cc_(flatten j));
constraint:=f*(genericElement)-sub(G_1,Bcc);
--Bflatmap:=last flattenRing(Bcc);
C := ((ZZ/p)[gens T|gens Bcc])[gens S];
Cflatmap:=inverse last flattenRing(C);
Cflat :=source Cflatmap;
J:=(inverse Cflatmap)( ideal last coefficients Cflatmap sub(constraint, Cflat));
elimList := (for i in gens Bcc list sub(i,Cflat))|(for i in gens S list sub(i,Cflat));
sub(eliminate(elimList,J),(ZZ/p)[gens T])
)




--
--)



evalMap=method()
evalMap(List,Ideal,Ring):= (L,I,T)->(
S:=ring I;
if length L != numgens S then return "error: needed a list with as many entries as the variables of S";
--mapVals:=for i from 0 to numgens S - 1 list (S_i-(L_i)_S);
map(S/I,T,L|gens S)
)


