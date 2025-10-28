newPackage(
    "WittVectors",
    Version => "0.01",
    Date => "December 4, 2023",
    Authors => {
    	{Name => "Anne Fayolle", Email => "anne.fayolle@utah.edu", HomePage => "https://annefayolle.github.io/"},
	{Name => "Abhay Goel", Email => "u1421426@utah.edu", HomePage => "https://faculty.utah.edu/u1421426-ABHAY_GOEL/teaching/index.hml"},
	{Name => "Devlin Mallory", Email => "malloryd@math.utah.edu", HomePage => "https://www.math.utah.edu/~malloryd/"},
	{Name => "Eamon Quinlan-Gallego", Email => "eamon.quinlan@utah.edu", HomePage => "https://eamonqg.github.io/"},
    	{Name => "Teppei Takamatsu", Email => "teppeitakamatsu.math@gmail.com", HomePage => "https://sites.google.com/view/teppei-takamatsu/home"}
    },
    Headline => "A Macaulay2 package for Witt vectors",
    Keywords => {"Witt Vectors"},
    DebuggingMode => true,
    Reload => true,
    AuxiliaryFiles => true
    )

export{
"rld",
"witt",
"wittOverring",
--"wittVectors",
"WittRingElement",
"wittTupleToOverring",
"wittTupleToRing",
"wittRingToTuple",
"wittOverringToTuple",
"verschiebung",
"wittOverringIdeal",
"wittRingIdeal",
"unWitt",
"overringMap",
"WittRing",
"wittSub",
"wittOverrings",
"WittPolynomialRing",
"WittRingMap",
"baseMap",
"WittQuotientRing",
"explicit",
"wittLength",
"wittRings",
"WittIdeal",
"wittIdeal",
"wittGenerators",
"explicitOver",
"MaxHeight",
"Nontrivial",
"PerturbationTerm",
"findFrobeniusLiftConstraints",
"findFrobeniusLift",
"createEquations",
"table2", --MAYBE
"fSplittingHeight",
"overring",
"wittFrobenius",
"truncation",
"makeCoefficientFieldPrime",
}

protect tuple

needsPackage "TestIdeals"
needsPackage "Polyhedra"
needsPackage "PushForward"
needsPackage "SLPexpressions"
needsPackage "MinimalPrimes"
needsPackage "Elimination"
rld = () -> (loadPackage "WittVectors")
load "./WittVectors/WittConstructor.m2"
load "./WittVectors/Kernels.m2"
load "./WittVectors/WittConversion.m2"
load "./WittVectors/FrobeniusLiftings.m2"
load "./WittVectors/QuasiFSplittings.m2"
load "./WittVectors/tests.m2"



---NEW TO DO

---5. decide about explicit witt ring class
---7. method for WR -> R? (currently available as WR.unWitt) likewise wittLength (DONE; but unprotected unWitt!!)
---9. make everything work over (finite) non prime fields.
---10. decide what to do about defunct files in directory
---11. where does breakString belong?
---12. Joyal coordinates?
---13. Cache wittTupleToOverring of witt vectors?


---TO DO
---1. Debug level for addition/multiplication/etc
---2. Functoriality
---3. fix kernelZZ to be more robust (should be able to get rid of degree check in wittTupleToRing)
---4. implement test for non-defined maps
---5. in wittOverringToTuple, does going mod a smaller power of p speed things up?

---7. New classes: WittVector(call this WittElement?), WittRing, WittIdeal, WittMap(?).
--- Put these in WittConstructor
--- All these should have .element, .ring, etc... to get the gross representations.
--- Change names of current methods to address this.
--- Implement methods for WittElement, WittRing, WittIdeal, WittMap, etc...

--- Classes to be implemented:
--- WittPolynomialRing (done)
--- WittQuotientRing
--- WittRingElement -- evaluate on a polynomial
--- WittRingMap
--- WittIdeal (ideal) -- exponentiation, generators, numgens, 
--- WittMatrix
--- WittModule
---
--- All custom keys should go in the constructor of the custom class.

--- Methods to implement: (only involve the witt ring if necessary; overring is easier)
--- ring
--- map
--- kernel (??), cokernel
--- operations on ideals
--- quotients of rings
--- trim
--- gens
--- 

--- Possible new directions: compute pushout of modules from queasi-F-split. 
--- Test for quasi-F-split for non complete intersections?
--- Frobenius lifts (rings are themselves over W_n).

--- 8. Implement for all finite fields (not just F_p for prime p)



breakString = method()
breakString(String) := s -> (
    usLocation := select(length s - 1, i -> s_i == "_");
    if length usLocation > 1 then(return "error: two underscores in string");
    usLocation = first usLocation;
    (substring(s, 0, usLocation), substring(s, usLocation + 1, length s - 1))
	)

beginDocumentation()

load "./WittVectors/Documentation.m2"
