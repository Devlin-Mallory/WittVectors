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
	
dumbWitt = (n, R) -> (
    p := char R;
    d := numgens R;
    Rvars := flatten entries vars R;
    
    ---
    cubes0 := for i in 0..(d-1) list ((0,toList((i:0)|(1:1)|((d-i-1):0))));
    cubes := for i in 1..(n-1) list (
	--print "hola";
	ind := (toList (0..(p^i-1)))^d;
	ind = delete(toList(d:0) , ind);
	{i}**ind
	--{k,every tuple of length d with values 0..p^k-1}
	);
    cubes = cubes0 | (flatten cubes);
    
    T := symbol T;
    A := ZZ[for i in cubes list T_i, Degrees => for i in cubes list i#0];
    B := QQ[for i in cubes list T_i, Degrees => for i in cubes list i#0];
    
    --goodvarsA := apply(select(cubes, ik -> ik#0 > 0), i -> T_i);
    

    --varsA := flatten entries vars A;
    dg := flatten entries basis(n, B);
    for aa in n..(2*n-2) do(
	dg := flatten entries basis (aa,B);
	B = (flattenRing(B / (ideal dg)))#0;
	dga := apply(dg, xx -> sub(xx, A));
	A = (flattenRing(A / (ideal dga)))#0;
	);
        
    use A;
    --for aa from 0 to n do(
--	biglist := apply(goodvarsA^(n-aa), product);
--	biglist = unique biglist;
--	biglist = apply(biglist, xx -> p^aa*xx);
--	dg = dg | biglist;
--	);
    --dg;
    
    -- 
    dg2 := apply(select(cubes, ik -> (0 < ik#0) and (ik#0 <= n-2)), ik ->
	p*T_ik - T_( ik#0 + 1 , apply(ik#1 , xx -> xx*p )) )  ;

    A = (flattenRing(A / ideal(dg2)))#0;
    
    A
    )
--S := ZZ[T

end

loadPackage "WittVectors"
R = GF(3)[x,y]
WR = explicit (witt(2, R))
si = ideal WR
di = dumbWitt(R, 2)

phi = map(ring di, ring si, 

for xx in 0..19 do(
    print "-----------";
    print xx;
    print (flatten entries vars W)#xx;
    print (flatten entries vars D)#xx;
    --print (phi((flatten entries vars D)#xx) - (flatten entries vars W)#xx);
    )
