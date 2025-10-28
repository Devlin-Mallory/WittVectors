-- export{
-- "witt",
-- "wittOverring",
-- --"wittVectors",
-- "WittRingElement",
-- "wittTupleToOverring",
-- "wittTupleToRing",
-- "wittRingToTuple",
-- "wittOverringToTuple",
-- "verschiebung", X 
-- "wittOverringIdeal",
-- "wittRingIdeal",
-- "unWitt",
-- "overringMap",
-- "WittRing",
-- "wittSub",
-- "wittOverrings",
-- "WittPolynomialRing",
-- "WittRingMap",
-- "baseMap",
-- "WittQuotientRing",
-- "explicit",
-- "wittLength",
-- "wittRings",
-- "WittIdeal",
-- "wittIdeal",
-- "wittGenerators",
-- "explicitOver",
-- "MaxHeight",
-- "Nontrivial",
-- "findFrobeniusLiftConstraints",
-- "findFrobeniusLift",
-- "createEquations",
-- "table2", --MAYBE
-- "fSplittingHeight",
-- "overring",
-- "wittFrobenius", X
-- "truncation",
-- "makeBaseFieldPrime",
-- }


--doc ///
--    Key 
--        WittVectors
--///
--
--
--doc ///
--    wittOverring
--///
--
--doc ///
--    wittTupleToOverring
--///
--
--doc /// 
--    wittVectors
--///
--
--doc ///
--    wittTupleToRing
--///
--
--doc ///
--    wittRingToTuple
--///
--
--doc ///
--    wittOverringToTuple
--///
--    
--doc ///
--    wittOverringIdeal
--///


-------------------------
--- witt method
-------------------------

-- Eamon: this gives an error; please fix?
-- doc ///
--     Key
-- 	(witt, ZZ, RingMap)
-- 	(witt, ZZ, ZZ, RingMap)
--     Usage
-- 	witt(n, R)
-- 	witt(m,k,R)
--     Inputs
-- 	n: ZZ
-- 	m: ZZ
-- 	k: ZZ
-- 	f: RingMap
--     Outputs
-- 	Wf: WittRingMap
--     Description
-- 	Text
-- 	    Given $f: R \to S$ a RingMap between rings  of positive characteristic and an integer
-- 	    $n \geq 1$, witt(n, f) returns the WittRingMap $W_n(f): W_n(R) \to W_n(S)$.
-- 	    If two integers $m \geq n \geq 1$ are passed, witt(n, m, f) returns the WittRingMap
-- 	    given by the composition $W_m(R) \to W_m(S) \to W_n(S)$, where the last map is
-- 	    truncation.
-- 	Example
-- 	    R = (ZZ/5)[x,y];
-- 	    S = (ZZ/5)[a,b,c,d];
-- 	    f = map(S, R, {a*b, c*d});
-- 	    witt(2, f)
-- 	    witt(2, 3, f)
-- ///


doc ///
    Key
	(witt, ZZ, PolynomialRing)
    Usage
	witt(n, R)
    Inputs
	n: ZZ
	R: PolynomialRing
    Outputs
	:WittPolynomialRing
    Description
	Text
	    Given an integer $n \geq 1$ and a polynomial ring $R$ of positive prime characteristic,
	    this produces the $n$-th witt ring $W_n(R)$ of $R$.
	Example
	    R = (ZZ/3)[x,y,z];
	    WR = witt(2, R)
///


doc ///
    Key
	(witt, ZZ, QuotientRing)
    Usage
	witt(n, R)
    Inputs
	n: ZZ
	R: QuotientRing
    Outputs
	:WittQuotientRing
    Description
	Text
	    Given an integer $n \geq 1$ and a quotient ring $R$ of positive prime characteristic,
	    this produces the $n$-th witt ring $W_n(R)$ of $R$.
	Text
	    Note that for this method to work, the ambient ring of $R$ must be a polynomial ring.
	    If this is not the case, consider flattening before applying witt.
	Example
	    R = (ZZ/3)[x,y,z] / ideal(x^2, y^2, z^2);
	    WR = witt(2, R)
	Example
	    S = (ZZ/2)[x,y,z] / ideal(x^2);
	    R = S / ideal(y^2, z^2);
	    WR = witt(2, (flattenRing R)#0)

///
	



doc ///
    Key
	(witt, List)
    Usage
	witt L
    Inputs
	L: List
	    a list of elements of the same ring of positive characteristic
    Outputs
	:WittRingElement
    Description
	Text
	    Given a list  $L = \{x_1, \dots , x_n\}$ of elements of the same
	    ring $R$ of positive prime characteristic, this produces the WittRingElement
	    $(x_1, \dots , x_n) \in W_n(R)$.
	Example
            R = ZZ/5[x,y,z]/(x^3 + y^3 + z^3);
            x + y
///


-------------------------
--- wittOverring
-------------------------


doc ///
    Key
	wittOverring
	(wittOverring, ZZ, Ring)
    Usage
	wittOverring(n, R)
    Inputs
	n: ZZ
	R: Ring
    Outputs
	:Ring
    Description
	Text
	    Given a polynomial ring $R = \mathbb{F}_p [x_1, \dots , x_n]$ over a
	    finite prime field $\mathbb{F}_p$, and an integer $n \geq 1$, it returns
	    and appropriately caches the polynomial ring $(ZZ / p^n)[T_1, \dots , T_n]$, which
	    we call the wittOverring. The reason is that the $n$-th Witt ring of $R$ is a subring
	    of this wittOverring.
	Example
	    R = (ZZ/2)[x,y];
	    wittOverring(3, R)
///	    



----
----
----


doc ///
    Key
	(toList, WittRingElement)
    Usage
	toList(w)
    Inputs
	w: WittRingElement
    Outputs
	:List
    Description
	Text
	    Turns a WittRingElement back into a list.
	Example
	    R = (ZZ/5)[x,y];
	    w = witt{x,y, x + y};
	    toList(w)
///

doc ///
    Key
	(ring, WittRingElement)
    Usage
	ring(w)
    Inputs
	w: WittRingElement
    Outputs
        R: --add??
    Description
	Text
	    Returns the WittPolynomialRing or WittQuotientRing that the input belongs to.
	Example
	    R = (ZZ/5)[x,y]
	    w = witt{x, x+y}
	    ring(w)
	Example
	    R = (ZZ/5)[x,y,z] / ideal(x^2 + y^2 + z^2)
	    w = witt{x, y, z}
	    ring(w)
///
	    
	    


--------------------------------
---------
--------------------------------

doc ///
    Key
	WittRingElement
    Headline
	The Type for elements of WittPolynomialRing and WittQuotientRing.
    Description
	Text
	    Instances of WittRingElement can be built by using the witt method.
	Example
	    R = (ZZ/3)[x,y];
	    w = witt{x^2 + y^2, x}
///
	


doc///
	Key
	 truncate
	Headline 
	 Crop Witt Vector to have a given length.
	Usage 
	 truncate(i, w)
	Inputs
	 i: ZZ
	 w: WittRingElement
	Outputs
	 v: WittRingElement
	Description
         Text
	    This crops w to have length i if i is less than or equal than the length of w.
	  Example
	    S=ZZ/3[x,y]
	    w=witt{x,y}
	    truncate(1,w)
	 Text
	  This should give {x}, a WittRingElement
	 Text 
	  We get an error if we try to truncate to something longer. For instance,  truncate(3,w) above would return an error.
///


doc ///
	Key
	 fSplittingHeight
	Headline
	 Finds the quasi-F-split height ht(S/I) of the quotient of the polynomial ring S=ZZ/p[x1,...,xn] by an ideal I generated by a regular sequence (f1,...,fm).
	Usage
	 fSplittingHeight I
	Inputs
	 I: Ideal
	Outputs
	 r: Number
	Description
	 Text
	    This gives the quasi-F-Splitting height r of S/I
	 Example
	    S = ZZ/3[x,y,z, w]
       	    I = ideal(x^4 + y^4 + z^4 + w^4 + x^2*z^2 + x*y*z^2)
	    fSplittingHeight I
	 Text
	    This should give 4. 
	 Example
		S = ZZ/3[x,y,z,w]
		S = ZZ/3[x,y,z,w]
       	        I = ideal(x^4 + y^4 + z^4 + w^4)
	        fSplittingHeight I
	 Text
	    This should give infinity. 
	 Example
	    S = ZZ/3[x,y,z]
       	    I = ideal(x,y)
	    fSplittingHeight I
	 Text

	 --Let's please keep this commented while we are working on the package.
	 -- Example 
	 -- 	S = (ZZ/2)[x,y,z,w,u]
	 -- 	I = ideal(x^5 + y^5 + z^5 + w^5 + u^5 + x*z^3*w + y*z*w^3 + x^2*z*u^2 + y^2*z^2*w + x*y^2*w*u + y*z*w*u^2)
	 -- 	fSplittingHeight I
	 -- Text
	 --    This should give 60
	 Example 
		S = ZZ/5[x,y,z]
		I = ideal(y*x,z*x)
	 	fSplittingHeight I
	 Text
	    We get an error since the ideal is not generated by a regular sequence
	 Example
		S = GF(4)[x,y,z]
		I=ideal(x)
		fSplittingHeight I
	 Text
	    We get an error since S is not a polynomial ring over ZZ/p.
	
///


doc ///
    Key
	(wittFrobenius, WittPolynomialRing)
	(wittFrobenius, WittQuotientRing)
    Usage
    	phi = wittFrobenius W
    Inputs
	W:{WittPolynomialRing, WittQuotientRing}
	   The Witt ring of a ring R of positive characteristic
    Outputs
	phi:WittRingMap
            the Frobenius map on W
    Description
	Text
            This gives the Frobenius map on the Witt ring W (which in coordinates is just the entry-wise Frobenius)
	Example
            R = ZZ/5[x]
            W = witt(2,R);
            phi = wittFrobenius W;
///

doc ///
    Key
	(wittFrobenius, ZZ, Ring)
    Usage
	phi = wittFrobenius(n, R)
    Inputs
        n:ZZ
           a positive integer, the length of the Witt vectors to consider
        R:Ring
            a ring of positive characteristic
    Outputs
	phi:WittRingMap
            the Frobenius map on witt(n,R)
    Description
	Text
            given a ring R and an integer n this gives the Frobenius map on W_n(R) (which in coordinates is just the entry-wise Frobenius)
	Example
            R = ZZ/5[x]
            phi = wittFrobenius(2,R)
///

doc ///
    Key
	(wittFrobenius, WittRingElement)
    Usage
	Fw = wittFrobenius w
    Inputs
	w:WittRingElement
           an element of a Witt ring
    Outputs
        Fw:WittRingElement
            the image of w under the Frobenius map
    Description
	Text
            Given a Witt vector w, this gives the image w under the Frobenius map (which in coordinates is just the entry-wise Frobenius)
	Example
            R = ZZ/5[x,y,z]
            w = witt{x,y,z}
            wittFrobenius(w) -- same as (wittFrobenius(R))(w)
///

doc ///
    Key
	(verschiebung, WittRingElement)
    Usage
	Vw = verschiebung w
    Inputs
	w:WittRingElement
           an element of a Witt ring
    Outputs
        Vw:WittRingElement
            the image of w under the Verschiebung map
    Description
	Text
            Given a Witt vector w, this gives the image w under the Verschiebung map (which in coordinates simply prepends a zero)
	Example
            R = ZZ/5[x,y]
            w = witt{x,y}
            verschiebung(w) -- same as wittFrobenius(w)
///

doc ///
    Key
	(symbol +, WittRingElement, WittRingElement)
    Usage
	w = w1+w2
    Inputs
	w1:WittRingElement
	w2:WittRingElement
           elements of a Witt ring
    Outputs
        w:WittRingElement
            the sum of w1 and w2
    Description
	Text
            Given Witt vectors w1 and w2, this computes their sum (corresponding to the addition operation inherited via the ghost maps)
	Example
            R = ZZ/5[x,y,z,w]
            w1 = witt{x,y}
            w2 = witt{z,w}
            w1+w2
///

doc ///
    Key
	(symbol *, WittRingElement, WittRingElement)
    Usage
	w = w1*w2
    Inputs
	w1:WittRingElement
	w2:WittRingElement
           elements of a Witt ring
    Outputs
        w:WittRingElement
            the product of w1 and w2
    Description
	Text
            Given Witt vectors w1 and w2, this computes their sum (corresponding to the multiplication operation inherited via the ghost maps)
	Example
            R = ZZ/5[x,y,z,w]
            w1 = witt{x,y}
            w2 = witt{z,w}
            w1*w2
///


document { Key => WittPolynomialRing,
    SeeAlso => {WittRing},
    Headline => "the class of Witt rings of a polynomial ring",
    EXAMPLE lines ///
      S = (ZZ/3)[x,y]
      W2S = witt(2,S)
    ///
    }


-- Eamon: this gives an error when not commented.
-- document {
--     Key => {findFrobeniusLift, (RingElement, ZZ)},
--     Headline => "find a lift of the Frobenius",
--     Usage => "findFrobeniusLift(d, f)",
--     Inputs => {"(d,f)"},
--     Outputs => {{"find a lift of the Frobenius on the ring", TT "W_2(S/f)" "using polynomials of degree", TT " < d+1"}},
-- 	Text This methods tries random polynomials of the given degree and checks if they give Frobenius lifts. This might not terminate since there might not be one that is a Frobenius lift.
--     Example 
-- 		S = (ZZ/2)[x,y]
-- 		I = ideal(x^2 +y^3)
-- 		L = findFrobeniusLift(2,I)
-- 	Text This should give a list whose second entry is y^2
-- 	Text To see which options the algorithm is trying, set verbose to true
-- 	Example 
-- 		S = (ZZ/2)[x,y]
-- 		I = ideal(x^3+y^5)
-- 		findFrobeniusLift(2,I,Verbose=>true)
-- 	Text This can give a couple of values like (x^2,0) or (0,y^2). Time and number of tries will vary since the polynomials the algorithm tries are random.
-- 	Text If there is no Frobenius lift, the algorithm will run without ending. 
-- 		Example S= (ZZ/7)[x,y,z]
-- 		I= ideal(x^3+y^3+z^3)
-- 		L= findFrobeniusLift(14,I)
-- 	Text This will not end. By Serre-Tate, there is only one (canonical) lifting of S/I that has a Frobenius morphism compatible with that of S/I. However, this is not the lifting we are working with.
--     ///
--     }



--- This gives error when uncommented.
-- doc ///
-- 	Key
-- 	 fSplittingHeight
-- 	Headline
-- 	 Finds the quasi-F-split height ht(S/I) of the quotient of the polynomial ring S=ZZ/p[x1,...,xn] by an ideal I generated by a regular sequence (f1,...,fm).
-- 	Usage
-- 	 fSplittingHeight I
-- 	Inputs
-- 	 I: Ideal
-- 	Outputs
-- 	 : r
-- 	Description
-- 	 Text
-- 		This gives the quasi-F-Splitting height r of S/I
-- 	Example
-- 		S = ZZ/3[x,y,z]
--        	        I = ideal(x^4 + y^4 + z^4 + w^4 + x^2*z^2 + x*y*z^2)
-- 	        fSplittingHeight I
-- 	 Text This should give 4. 
-- 	 Example
-- 		S = ZZ/3[x,y,z]
--        	        I = ideal(x^4 + y^4 + z^4 + w^4)
-- 	        fSplittingHeight I
-- 	 Text This should give infinity. 
-- 	 Example
-- 		S = ZZ/3[x,y,z]
--        	I = ideal(x,y)
-- 	    fSplittingHeight I
-- 	 Text This should give 1. 
-- 	 Example 
-- 		 S = (ZZ/2)[x,y,z,w,u]
-- 		 I = ideal(x^5 + y^5 + z^5 + w^5 + u^5 + x*z^3*w + y*z*w^3 + x^2*z*u^2 + y^2*z^2*w + x*y^2*w*u + y*z*w*u^2)
-- 		 fSplittingHeight I
-- 	 Text This should give 60
-- 	 Example 
-- 		 S = ZZ/5[x,y,z]
-- 		 I = ideal(y*(1-x),z*(1-x))
-- 	 	 fSplittingHeight I
-- 	 Text We get an error since the ideal is not generated by a regular sequence
-- 	 Example
-- 		 S = GF(4)[x,y,z]
-- 		 I=ideal(x)
-- 		 fSplittingHeight I
-- 	Text We get an error since S is not a polynomial ring over ZZ/p.
-- 	SeeAlso
-- ///


-- doc ///
-- 	Key
-- 	 findFrobeniusLiftConstraints
-- 	Headline
-- 	 Finds the restrictions of the delta structures on a ring R
-- 	Usage
-- 	 findFrobeniusLiftConstraints I
-- 	Inputs
-- 	 I: Ideal
--      	 R: ring I, R is a polynomial ring
-- 	Outputs
-- 	 : (g_1(x_1,...,x_n,aa_1,...,aa_n),...,g_s(x_1,...,x_n,aa_1,...,aa_n))
-- 	Description
-- 	 Text
-- 		This gives constraints on the values of aa_i=delta(x_i) for them to descend to R/I
-- 		If I is generated by s elements, there are at most s constraints, given by g_j and the values of aa_i that make all g_j(x_1,...,x_n,aa_1,...,aa_n) vanish on R/I are the possible values for delta(x_i)
-- 	 Example
-- 		R=ZZ/2[x,y]
--        	        f=x^2-y^3
-- 	        findFrobeniusLiftConstraints(f)
-- 	 Text Here, delta(x) can be anything but delta(y) has to be in the ideal y^2+(f). 
-- 	 Example
-- 	 	R=ZZ/5[x,y]
-- 		f=2y^3+x^2
-- 		findFrobeniusLiftConstraints(f)
-- 	 Text Here, we get that delta(x)x^5-delta(y)x^6y-x^10 has to be 0. 
-- 	 Example 
-- 		 R=ZZ/2[x,y,z]
-- 		 f=x^3+y^3+z^3
-- 		 findFrobeniusLiftConstraints(f)
-- 	 Text Here, we will find constraints even though there is no solution. 
-- 	 Example 
-- 		 R=ZZ/5[x,y,z]
-- 		 I=ideal(2*y^3+x^2,3*z^5-x^3)
-- 	 	 findFrobeniusLiftConstraints(I)
-- 	 Text We find an ideal generated by two elements
-- 	SeeAlso
	
-- ///


end



