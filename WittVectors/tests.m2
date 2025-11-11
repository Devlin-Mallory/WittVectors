
TEST ///
witt(2,ZZ/3)
witt(2,ZZ/3[x])
witt(2,ZZ/5[x]/x^2)
witt(2,GF 9)
witt(2, (GF 9)[x])
witt(2, (GF 9)[x]/x^2)
assert( (try witt(2,ZZ/15)) == null)
assert( (try witt(2,QQ)) == null)
assert( (try witt(2,QQ[x])) == null)
///

--TEST /// -- Check that the fSplittingHeight method gives back the correct number
--    for i from 1 to 11 do (
--        I=ideal table2(i);
--        j=i;
--        if i==6 or i==11 then j=infinity;
--        assert(fSplittingHeight(I)==j)
--    )
--    ///

TEST ///
    S = (ZZ/5)[x,y]
    I = ideal(x^2-y^3)
    R = S/I
    W2S = witt(2,S)
    W2R = witt(2,R)
    assert(char(W2S.overring) == 25)
    assert(char(W2R.overring) == 25)
///



TEST ///
    S = (ZZ/5)[x_1,x_2,x_3,y_1,y_2,y_3]
    W3S = witt(3,S)
    w1 = witt{x_1,x_2,x_3}
    w2 = witt{y_1,y_2,y_3}
    w1+w2 == witt{x_1+y_1, -x_1^4*y_1-2*x_1^3*y_1^2-2*x_1^2*y_1^3-x_1*y_1^4+x_2+y_2, -x_1^24*y_1-2*x_1^23*y_1^2-2*x_1^22*y_1^3-x_1^21*y_1^4-2*x_1^19*y_1^6+2*x_1^18*y_1^7+x_1^16*y_1^9-x_1^13*y_1^12-x_1^12*y_1^13+x_1^9*y_1^16+2*x_1^7*y_1^ 18-2*x_1^6*y_1^19-x_1^4*y_1^21-2*x_1^3*y_1^22-2*x_1^2*y_1^23-x_1*y_1^24-x_1^16*x_2*y_1^4+2*x_1^15*x_2*y_1^5-2*x_1^14*x_2*y_1^6+x_1^13*x_2*y_1^7-2*x_1^ 11*x_2*y_1^9-2*x_1^10*x_2*y_1^10-2*x_1^9*x_2*y_1^11+x_1^7*x_2*y_1^13-2*x_1^6*x_2*y_1^14+2*x_1^5*x_2*y_1^15-x_1^4*x_2*y_1^16-x_1^16*y_1^4*y_2+2*x_1^15*y _1^5*y_2-2*x_1^14*y_1^6*y_2+x_1^13*y_1^7*y_2-2*x_1^11*y_1^9*y_2-2*x_1^10*y_1^10*y_2-2*x_1^9*y_1^11*y_2+x_1^7*y_1^13*y_2-2*x_1^6*y_1^14*y_2+2*x_1^5*y_1^ 15*y_2-x_1^4*y_1^16*y_2+2*x_1^12*x_2^2*y_1^3+2*x_1^11*x_2^2*y_1^4+x_1^10*x_2^2*y_1^5+x_1^8*x_2^2*y_1^7+x_1^7*x_2^2*y_1^8+x_1^5*x_2^2*y_1^10+2*x_1^4*x_2 ^2*y_1^11+2*x_1^3*x_2^2*y_1^12-x_1^12*x_2*y_1^3*y_2-x_1^11*x_2*y_1^4*y_2+2*x_1^10*x_2*y_1^5*y_2+2*x_1^8*x_2*y_1^7*y_2+2*x_1^7*x_2*y_1^8*y_2+2*x_1^5*x_2 *y_1^10*y_2-x_1^4*x_2*y_1^11*y_2-x_1^3*x_2*y_1^12*y_2+2*x_1^12*y_1^3*y_2^2+2*x_1^11*y_1^4*y_2^2+x_1^10*y_1^5*y_2^2+x_1^8*y_1^7*y_2^2+x_1^7*y_1^8*y_2^2+ x_1^5*y_1^10*y_2^2+2*x_1^4*y_1^11*y_2^2+2*x_1^3*y_1^12*y_2^2-2*x_1^8*x_2^3*y_1^2+2*x_1^7*x_2^3*y_1^3-x_1^6*x_2^3*y_1^4-x_1^4*x_2^3*y_1^6+2*x_1^3*x_2^3* y_1^7-2*x_1^2*x_2^3*y_1^8-x_1^8*x_2^2*y_1^2*y_2+x_1^7*x_2^2*y_1^3*y_2+2*x_1^6*x_2^2*y_1^4*y_2+2*x_1^4*x_2^2*y_1^6*y_2+x_1^3*x_2^2*y_1^7*y_2-x_1^2*x_2^2 *y_1^8*y_2-x_1^8*x_2*y_1^2*y_2^2+x_1^7*x_2*y_1^3*y_2^2+2*x_1^6*x_2*y_1^4*y_2^2+2*x_1^4*x_2*y_1^6*y_2^2+x_1^3*x_2*y_1^7*y_2^2-x_1^2*x_2*y_1^8*y_2^2-2*x_ 1^8*y_1^2*y_2^3+2*x_1^7*y_1^3*y_2^3-x_1^6*y_1^4*y_2^3-x_1^4*y_1^6*y_2^3+2*x_1^3*y_1^7*y_2^3-2*x_1^2*y_1^8*y_2^3+x_1^4*x_2^4*y_1+2*x_1^3*x_2^4*y_1^2+2*x _1^2*x_2^4*y_1^3+x_1*x_2^4*y_1^4-x_1^4*x_2^3*y_1*y_2-2*x_1^3*x_2^3*y_1^2*y_2-2*x_1^2*x_2^3*y_1^3*y_2-x_1*x_2^3*y_1^4*y_2+x_1^4*x_2^2*y_1*y_2^2+2*x_1^3* x_2^2*y_1^2*y_2^2+2*x_1^2*x_2^2*y_1^3*y_2^2+x_1*x_2^2*y_1^4*y_2^2-x_1^4*x_2*y_1*y_2^3-2*x_1^3*x_2*y_1^2*y_2^3-2*x_1^2*x_2*y_1^3*y_2^3-x_1*x_2*y_1^4*y_2 ^3+x_1^4*y_1*y_2^4+2*x_1^3*y_1^2*y_2^4+2*x_1^2*y_1^3*y_2^4+x_1*y_1^4*y_2^4-x_2^4*y_2-2*x_2^3*y_2^2-2*x_2^2*y_2^3-x_2*y_2^4+x_3+y_3}
    w1*w2 == witt{x_1*y_1, x_2*y_1^5+x_1^5*y_2, -x_1^5*x_2^4*y_1^20*y_2-2*x_1^10*x_2^3*y_1^15*y_2^2-2*x_1^15*x_2^2*y_1^10*y_2^3-x_1^20*x_2*y_1^5*y_2^4+x_3*y_1^25+x_1^25*y_3+x_2^5*y_2^5}
///


TEST ///
    S = (ZZ/3)[x,y,z,w]
    I = ideal(x^2+y^2+z^2+w^2, x*y+x*z+x*w+y*z+y*w+z*w)
    n = 3
    d = 3
    J = wittOverringIdeal(n, I)
    f = for i from 0 to n-1 list random(d, I)
    assert isSubset(ideal wittTupleToOverring witt f, J)
///

TEST ///
    S = (ZZ/5)[x_1,x_2,x_3,y_1,y_2,y_3]
    W3S = witt(3,S)
    w1 = witt{x_1,x_2,x_3}
    wittFrobenius(w1) == witt{x_1^5,x_2^5,x_3^5}
///


TEST ///
    S = (ZZ/2)[x,y]
    f = x^2 + y^3
    I = ideal(f)
    J = findFrobeniusLiftConstraints(I)
    c=(entries vars ring J)#0#1
    use ring J
    J == ideal(c*x^2*y+x^4)
///


TEST ///
    S = (ZZ/2)[x,y]
    f = x^2 + y^3
    I = ideal(f)
    L = findFrobeniusLift(2,I)
    L#1 == y^2
///



TEST ///
    S = (ZZ/3)[x,y]
    w = witt{x,x^2}
    R = S/x
    p = map(R,S)
    Wp = witt(2,p)
    Wp(w) == witt{0_R,0_R}
    w21 = witt(1,2,id_S)
    assert((try w21^2) == null)
    assert((try w21*w21) == null)
    use S
    f = map(S,S,{x^2,y})
    Wf = witt(1,2,f)
    explicit Wf
///

TEST ///
R = GF(5)[x,y,z]
    f1 = random(3, R)
    f2 = random(2, R)
    f3 = random(4, R)
    tt = {f1, f2, f3}
    assert( witt tt == wittOverringToTuple wittTupleToOverring witt tt)
///

TEST ///
    R = GF(7)[x,y,z]
    WR = witt(3, R)
    w = witt{x,y,z}
    t = truncate(2, WR)
    assert( t(w) == witt{x,y})
///

TEST ///
R = ZZ/2
Rx = R[x]
B = Rx/(x^2)
R4 = GF 4
x=symbol x
Rx4 = R4[x]
B4 = Rx4/x^2


assert(R === unWitt witt(2,R))
assert(Rx === unWitt witt(2,Rx))
assert(B === unWitt witt(2,B))
assert(R4 === unWitt witt(2,R4))
assert(Rx4 === unWitt witt(2,Rx4))
assert(B4 === unWitt witt(2,B4))

assert(witt{1_R,0_R}+witt{0_R,1_R} == witt{1_R,1})
assert(witt{1_Rx,0_Rx}+witt{0_Rx,x_Rx} == witt{1_Rx,x_Rx})
assert(witt{1_B,0_B}+witt{0_B,x_B}  == witt{1_B,x_B})
assert(witt{a_R4+1,0_R4}+witt{0_R4,a_R4} == witt{a_R4+1,a_R4})
assert(witt{1_Rx4,0_Rx4}+witt{0_Rx4,x_Rx4} == witt{1_Rx4,x_Rx4})
assert(witt{1_B4,0_B4}+witt{0_B4,x_B4} == witt{1_B4,x_B4})

assert(numgens explicit witt(2,R) == 0)
assert(numgens explicit witt(2,Rx) == 2)
assert(numgens explicit witt(2,B) == 2)
assert(numgens explicit witt(2,R4) == 2)
assert(numgens explicit witt(2,Rx4) == 5)
assert(numgens explicit witt(2,B4) == 5)
///


TEST ///
S = ZZ/2[x,y]
I = ideal(x*y)
J = ideal(0_S)
dim createEquations(2,I,Homogeneous=>true) > 0
dim createEquations(2,I,Homogeneous=>true, PerturbationTerm=>{1}) < 0
dim createEquations(2,0_S,Homogeneous=>true) > 0
///
