
List ^ ZZ := (L, n) -> (
    if n <= 0 then( return {{}});
    output := apply(L, xx -> {xx});
    for i in 1..(n-1) do(
	output = (output**L);
	output = apply(output, toList);
	output = apply(output, flatten);
	);
    output
    )
	
dumbWitt = (R, n) -> (
    p := char R;
    d := numgens R;
    Rvars := flatten entries vars R;
    
    ---
    cubes := for i in 0..(n-1) list (
	--print "hola";
	{i}**((toList (0..(p^i-1)))^d)
	--{k,every tuple of length d with values 0..p^k-1}
	);
    cubes = flatten cubes;
    
    T := symbol T;
    A := ZZ[for i in cubes list T_i];

    goodvarsA := apply(select(cubes, ik -> ik#0 > 0), i -> T_i);
    

    --varsA := flatten entries vars A;
    dg := {};
    for aa from 0 to n do(
	biglist := apply(goodvarsA^(n-aa), product);
	biglist = unique biglist;
	biglist = apply(biglist, xx -> p^aa*xx);
	dg = dg | biglist;
	);
    --dg;
    
    dg2 := apply(select(cubes, ik -> ik#0 <= n-2), ik ->
	p*T_ik - T_( ik#0 + 1 , apply(ik#1 , xx -> xx*p )) )  ;

    alldg := dg | dg2;
    

    ideal(alldg)
    )
--S := ZZ[T

end

loadPackage "WittVectors"
R = GF(3)[x,y]
WR = explicit (witt(2, R))
si = ideal WR
di = dumbWitt(R, 2)

phi = map(ring di, ring si, 
