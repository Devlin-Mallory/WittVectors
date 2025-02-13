
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



document { Key => WittPolynomialRing,
    SeeAlso => {WittRing},
    Headline => "the class of Witt rings of a polynomial ring",
    EXAMPLE lines ///
      S = (ZZ/3)[x,y]
      W2S = witt(2,S)
    ///
    }

document {
    Key => {findFrobeniusLift, (RingElement, ZZ)},
    Headline => "find a lift of the Frobenius",
    Usage => "findFrobeniusLift(d, f)",
    Inputs => {"(d,f)"},
    Outputs => {{"find a lift of the Frobenius on the ring", TT "W_2(S/f)" "using polynomials of degree", TT " < d+1"}}
    EXAMPLE lines ///
    ///
    }


doc ///
	Key
	 findFrobeniusLiftConstraints
	Headline
	 Finds the restrictions of the delta structures on a ring R
	Usage
	 findFrobeniusLiftConstraints (f)
	Inputs
	 f: ringElement
     R: ring f
	Outputs
	 : (g_1,...,g_n)
	Description
	 Text
	 Example
	  
	 Text
	 Example
	 
	 Text
	 Example
	 Text
	 Example
	 Text	  
	SeeAlso
	
///
