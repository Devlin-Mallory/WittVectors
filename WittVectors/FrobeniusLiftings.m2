--TODO: add methods to check flatness of families over W(n,k), and to find liftings to these rings
--TODO: try to write down equations for Raynaud's example

--TODO: isFlatLift

--TODO: remove duplicated lines

--TODO: make this work for a nonprincipal ideal


findFrobeniusLift=method(Options=>{Nontrivial=>false, Homogeneous => false, Verbose=>false})

findFrobeniusLift(ZZ,RingElement) := opts -> (d,f) -> findFrobeniusLift(d, ideal f,opts)



findFrobeniusLift(ZZ,Ideal) := opts -> (d,I) ->(
    S := ring I;
    R := S/I;
    n := numgens S;
    J := findFrobeniusLiftConstraints(I);
    T := ring J;
    j := 0;
if not opts.Nontrivial then L :=toList((n):0) else L = for i from 0 to n-1 list if opts.Homogeneous == false then sum for i from 0 to d list random(i,S) else random(d,S);
    while (evalMap(L,I,T))(J) != 0 do ( if opts.Verbose then print j; j = j +1 ; L=
for i from 0 to n-1 list if opts.Homogeneous == false then sum for i from 0 to d list random(i,S) else random(d,S);
);
    apply(L,i->sub(i,R))
)


findFrobeniusLiftConstraints=method()
findFrobeniusLiftConstraints(RingElement) := (f) -> findFrobeniusLiftConstraints(ideal f)


findFrobeniusLiftConstraints(Ideal) := (I) ->(
S:=ring I;
R:=S/I;
d:=numgens S;
aa:=symbol aa;
T:=prune(S[aa_0..aa_(d-1)]);
TR:=T/sub(I,T);
trim sum for f in I_* list(
Cf:=apply(flatten entries last coefficients f, i->sub(i,ZZ));
Ef :=flatten( exponents\ flatten entries first coefficients f);
WCf:=(apply(Ef,i->product for j from 0 to d-1 list (witt{T_(d+j),T_j})^(i_j)));
sub(ideal last (sum flatten (for i from 0 to length Cf - 1 list Cf_i*WCf_i)).tuple, TR))
)



expandFrobeniusConstraints=method(Options=>{Homogeneous=>false})

expandFrobeniusConstraints(ZZ,RingElement) := opts -> (d,f) -> expandFrobeniusConstraints(d,ideal f, opts)

expandFrobeniusConstraints(ZZ,Ideal) := opts -> (d,J) -> (
S := ring J;
I := findFrobeniusLiftConstraints(J);
A := ring I;
n := dim ring J;
c := symbol c;
monomials := if opts.Homogeneous then 
    apply(select( latticePoints hypercube(n, 0, d),i->sum entries i == {d}),j->entries j) 
else
    apply(select( latticePoints hypercube(n, 0, d),i->sum entries i <= {d}),j->entries j) ;
B := S[flatten for i in monomials list for j from 1 to n list c_(flatten i ,{j})];
mapList := for j from 1 to n list sum apply(monomials,i->S_(flatten i)*c_(flatten i,{j}));
--expand:=map(B/sub(J,B),A,mapList|gens S);
--move the resulting ideal to B/fB?
expand:=map(B,A,mapList|gens S);
expand I
)

createEquations = method(Options => {Homogeneous => false})
createEquations(ZZ,RingElement) := opts -> (d,f)->createEquations(d,ideal f,opts)
createEquations(ZZ,Ideal) := opts -> (d,I) -> (
G:=expandFrobeniusConstraints(d,I,Homogeneous=>opts.Homogeneous);
n:=dim ring I;
S:=ring I;
p:=char S;
T:=ring G;
cc:=symbol cc;
monomials := if opts.Homogeneous then 
    apply(select( latticePoints hypercube(n, 0, d),i->sum entries i == {d}),j->entries j) 
else
    apply(select( latticePoints hypercube(n, 0, d),i->sum entries i <= {d}),j->entries j) ;
Bcc := T[flatten flatten for k1 from 0 to numgens G -1 list for k2 from 0 to numgens I -1 list for i in monomials list cc_(flatten i,{k1,k2})];
genericElement:=matrix for k1 from 0 to numgens G -1 list for k2 from 0 to numgens I -1 list sum apply(monomials,j->S_(flatten j)*cc_(flatten j,{k1,k2}));
constraint:=ideal((genericElement)*transpose gens I-transpose sub(gens G,Bcc));
--Bflatmap:=last flattenRing(Bcc);
C := ((ZZ/p)[gens T|gens Bcc])[gens S];
Cflatmap:=inverse last flattenRing(C);
Cflat :=source Cflatmap;
J:=ideal for j in constraint_* list (inverse Cflatmap)( ideal last coefficients Cflatmap sub(j, Cflat));
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


