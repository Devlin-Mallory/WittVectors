needsPackage "WittVectors"

RListToTuple = (T,p) ->(
n := length T;
R := new MutableList from {};
R#0 = T_0;
for j from 1 to n - 1 do(R#j = (T_j  - sum for i from 0 to j - 1 list p^i* R#i^(p^(j-1-i+1)))//p^j);
toList R
)

newAdd = (w1,w2) -> (
n := length w1;
S := (ring w1).unWitt;
p := char S;
subRing := prune((ZZ/p^n)(monoid S));
w1 = apply(w1.tuple, j-> sub(j, subRing));
w2 = apply(w2.tuple, j-> sub(j, subRing));
P := for i from 1 to n list sum for j from 1 to i list p^(j-1)*(w1)_(j-1)^(p^(i-j));
Q := for i from 1 to n list sum for j from 1 to i list p^(j-1)*(w2)_(j-1)^(p^(i-j));
T=P+Q;
RListToTuple(T,p)
)


end--
restart
load "AlternativeAlgorithm.m2"

p=3
S=(ZZ/p)[x_0..x_3,y_0..y_3]
n=2
d=4
--generic addition
--w1=witt{x_0,x_1,x_2,x_3}
--w2=witt{y_0,y_1,y_2,y_3}
w1=witt for i from 0 to n-1 list sum for j from 0 to d list random(j, S)
w2=witt for i from 0 to n-1 list sum for j from 0 to d list random(j, S)

elapsedTime(witt newAdd(w1,w2));
elapsedTime(w1+w2);
