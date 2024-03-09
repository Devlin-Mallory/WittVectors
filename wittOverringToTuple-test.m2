wott = method()
wott(RingElement) = (F)->(
    f:=F;
    OR := ring f;
    R := OR.cache.unWitt;
    d := numgens R;
    p := (radical ideal char OR)_0;
    --n := (log_p(char OR))^ZZ; 
    --the above line succeeds/fails very randomly: it works for p=5 and e=2, 4, and 5, but not 3 and 6
    n := floor(log_p(char OR));
    y:=symbol y;
    RY := R[y_0..y_(d-1)]/ideal(for i from 0 to d-1 list y_i^(p^(n-1))-R_i);
    -- This is not a real ring map!
    answer := {};
    for e from 0 to n-1 do (
        phi := map(RY, OR, for i from 0 to d-1 list y_i^(p^e));
        g := f%p;
        g0 :=elapsedTime sub(phi(g),R);
        answer = answer | {g0};
        --f = f - wittTupleToOverring(toList (e:0_R) | {g0} | toList (n-e-1:0_R));
        --the above line was giving the wrong answer for n > 2, while the below line seems to work
        f = elapsedTime( F - wittTupleToOverring(answer|toList(n-e-1:0_R)) );
        if (f%(p^(e+1)))!=0 then (
            error "Element of overring is not in the witt ring";
        );
        f = f//p^(e+1);
    );
    return witt(answer);
)


takeRoot = (f,n) -> (
    ---in a ring of char p, takes the (1/p^n) root of a polynomial f
    p := char ring f;
    mons := (coefficients f)#0;
    coeffs := (coefficients f)#1;
    --newmons := apply( flatten entries mons, xx -> 
)

takeRoot = (f, n) -> (
    --- in a ring of char p , takes the (1/p^n) root of a polynomial f
    R := ring f;
    p := char R;
    d := numgens R;
    RY := R[y_0 .. y_(d-1)] / ideal( for i from 0 to d-1 list y_i^(p^n) - R_i );
    Rsub := map( RY, R, toList( y_0..y_(d-1)) );
    sub(Rsub(f), R)
    )
	    
wott2 = method()
wott2(RingElement) = F -> (
    OR := ring F;
    R := OR.cache.unWitt;
    unWittSub := map(R, OR, vars R);
    (p, n) := (factor(char OR))#0;
    if n == 1 then(
	return witt{ unWittSub
    
