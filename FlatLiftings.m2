needsPackage "WittVectors"
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
trim ideal (sum for i in exponents f list product for j from 0 to d-1 list (witt{T_(d+j),T_j})^(i_j)).tuple
)

evalMap=method()
evalMap(List,Ideal,Ring):= (L,I,T)->(
S:=ring I;
if length L != numgens S then return "error: needed a list with as many entries as the variables of S";
--mapVals:=for i from 0 to numgens S - 1 list (S_i-(L_i)_S);
map(S/I,T,L|gens S)
)


