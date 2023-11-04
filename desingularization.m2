newPackage(
    "Desingularization",
    Version => "0.01",
    Date => "October 41, 2029",
    Authors => {
	{Name => "Daniel Apsley", Email => "apsley@math.utah.edu", HomePage => "https://faculty.utah.edu/u1421441-DANIEL_JONATHAN_APSLEY/research/index.hml"}, 
    {Name => "Emelie Arvidsson", Email => "u6041982@utah.edu", HomePage => "https://www.emeliearvidsson.com/"},
    {Name => "Joseph Sullivan", Email => "u1474923@math.utah.edu", HomePage => "https://partiallyordered.com/"}},
    Headline => "Resolving Singularities in Macaulay2",
    Keywords => {"Algebraic Geometry"},
    PackageImports => { "ReesAlgebra", "Divisor", "PrimaryDecomposition" },
    DebuggingMode => true,
    Reload=>true
    );

export {"variableChange", 
"preImage",
"inverseMap", 
"prunedringMap", 
"blowupCharts",
"totalTransform",
"strictTransform",
"isResolved",
"Exceptional"
};

-- Change the above as needed! We will probably take out a good chunk of these before submission. 

variableChange = method();
variableChange(PolynomialRing, Symbol) := (R, t) -> (
	oldVars := flatten entries vars R;
	n := #(oldVars);
	coeffRing := coefficientRing(R);
	freshRing := coeffRing[t_1..t_n];
	phi := map(freshRing, R, vars freshRing);
	phi
);

variableChange(QuotientRing, Symbol) := (R, t) -> (
	oldVars := flatten entries vars R;
	n := #oldVars;
	coeffRing := coefficientRing(R);
	freshPolyRing := coeffRing[t_1..t_n];
	psi := map(R, freshPolyRing, oldVars);
	freshIdeal := ker psi;
	freshRing := freshPolyRing/freshIdeal;
	phi := map(freshRing, R, vars freshRing);
	phi
);


variableChange(Ideal, Symbol) := (I, t) -> (
	R := ring(I);
	phi := variableChange(R, t);
	phi(I)
);

-- Perhaps the function finding the 'pruning map' exists already. I couldn't find it so I made some. Excuse the bit of space.

preImage = method();
preImage(RingMap, Ideal) := (phi, I) -> (
    projection := map(target(phi)/I, target(phi));
    kernel (projection*phi) 
);


inverseMap = method();
inverseMap(RingMap) := phi -> (
    if kernel phi != ideal(substitute(0, source phi)) then (
        error "The map is not invertible."
    );
    flatRing := (flattenRing(target phi))#0;
    varlist := flatten entries vars flatRing;
    images := {};
    for x in varlist do (
        J := preImage(phi, ideal(substitute(x, target phi)));
        gensJ := flatten entries gens J;
        images = append(images, gensJ#0);
    );
    map(source phi, target phi, images)
);

--TODO: add an error for when J is not principal. 

prunedringMap = method();
prunedringMap(QuotientRing) := R -> (
    prunedRing := prune R; 
    badvars := flatten entries vars prunedRing;
    goodvars := {};
    for x in badvars do (
        goodvars = append(goodvars, substitute(x, R))
    );
    phi := map(R, prunedRing, goodvars);
    inverseMap(phi)
);


blowupCharts = method(Options => {Exceptional => true});
blowupCharts(Ideal, ZZ) := opts -> (J, m) -> (
	a := reesIdeal(J); -- Ideal of rees algebra in affine space over A.
	A := ring(J);
	B := ring(a);
	StructureB := map(B, A, {});
	n := #gens B;

	if (m < 1) or (m > n) then (
		error "chart number out of range";
	);

	AffineRing := A[u_1..u_(n - 1)];
	structureMap := map(AffineRing, A, {});
	coolBeans := flatten flatten {toList(u_1..u_(m - 1)), 1, toList(u_m..u_(n - 1))};
	phi := map(AffineRing, B, coolBeans);
	quotient := AffineRing/phi(a);
	projection := map(quotient, AffineRing, {});
	outputMap := prunedringMap(quotient)*projection * structureMap;
    exceptionalIdeal := trim outputMap(J);
    if opts#Exceptional === true then (
        return {outputMap, exceptionalIdeal};
    );
    if opts#Exceptional === false then (
        return outputMap;
    );
);

-- TODO: Make the u in the above definition local, so that the package loads without error. 

blowupCharts(Ideal) := opts -> idealdude -> (
	listofCharts := {};
	for i from 1 to (#(flatten entries gens idealdude)) do (
		listofCharts = append(listofCharts, blowupCharts(idealdude, i, opts))
	);
	listofCharts
);

totalTransform = method();

totalTransform(Ideal, Ideal, ZZ) := (I, J, m) -> (
	chartMap := blowupCharts(J, m, Exceptional => false);
	chartMap(I)
);

totalTransform(Ideal, Ideal) := (I, J) -> (
	n := #(flatten entries gens J);
	outputlist := {};
	for i from 1 to n do (
		outputlist = append(outputlist, totalTransform(I, J, i));
	);
	outputlist
);

strictTransform = method(Options => {Exceptional => false});

strictTransform(Ideal, Ideal, ZZ) := opts -> (I, J, m) -> (
	idealList := primaryDecomposition(totalTransform(I, J, m));
    if (opts#Exceptional === true) then (
        return idealList;
    );
    if (opts#Exceptional === false) then (
        if (#idealList > 2) then (
            error "Expected irreducible ideal.";
        );
        return idealList#1;
    );
);

--TODO: Update this to be accurate, taking into account the fact that blowupCharts now tracks exceptional divisors. 


strictTransform(Ideal, Ideal) := opts -> (I, J) -> (
	n := #(flatten entries gens J);
	L := {};
	for i from 1 to n do (
		littleL := strictTransform(I,J,i,opts);
		L = append(L, littleL);
	);
	L
);


isResolved = method(Options => {Exceptional => false});

isResolved(Ideal, ZZ) := opts -> (I, n) -> (

);

-- TODO: make this function! 

beginDocumentation()

doc ///
    Key 
        prunedringMap
        (prunedringMap, QuotientRing)
    Headline
        the pruning isomorphism. 
    Usage
        prunedringMap(R)
    Inputs
        R: QuotientRing
    Outputs
        : RingMap
    Description
        Text
         Outputs the isomorphism between a quotient ring and its pruning.  
    SeeAlso

///

doc ///
    Key 
        blowupCharts
        (blowupCharts, Ideal, ZZ)
        (blowupCharts, Ideal)
        [blowupCharts, Exceptional]
    Headline
        Blowing up ideals of affine varieties. 
    Usage
        blowupChart(J, n, Exceptional => b)
        blowupChart(J)
    Inputs
        J: Ideal
        n: ZZ
        b: Boolean
    Outputs
        : List
        : List
    Description
        Text
         Finds the charts and exceptional divisors of the blowup of an affine scheme along an ideal. Outputs the n'th chart of the blowup of ring(J) along J. It will output a list of ring maps, together with ideals of the target which define the exceptional locus 
    SeeAlso

///

doc ///
    Key 
        totalTransform
        (totalTransform, Ideal, Ideal, ZZ)
        (totalTransform, Ideal, Ideal)
    Headline
        Transporting ideals along blowups.
    Usage
        totalTransform(I, J, n)
        totalTransform(I, J)
    Inputs
        I: Ideal
        J: Ideal
        n: ZZ
    Outputs
        : Ideal
        : List
    Description
        Text
         Computes the total transform of an ideal. If X' -> X is the blowup and a is the ideal, this computes the local description of a*O_X'.
    SeeAlso
        strictTransform
///

doc ///
    Key 
        strictTransform
        (strictTransform, Ideal, Ideal, ZZ)
        (strictTransform, Ideal, Ideal)
    Headline
        The non-exceptional part of the total transform. 
    Usage
        strictTransform(I, J, n)
        strictTransform(I, J)
    Inputs
        I: Ideal
        J: Ideal
        n: ZZ
    Outputs
        : Ideal
        : List
    Description
        Text
         Computes the strict transform of an ideal. That is, it factors the exceptional part out of the total transform.
    SeeAlso
        strictTransform
///


TEST ///
   
///



end--

-- T = QQ[x,y];
-- J = ideal(x,y);
-- I = ideal(x^3 - x^2 + y^2);

 -- I defines a nodal cubic resolved by one blow-up at the origin. The following command computes the ideal of the strict transform of I in the first chart.

-- strictTransform(I, J, 1)
-- T = QQ[x,y,z];
-- I = ideal(x^2*z - y^2); -- whitney umbrella

-- isResolved(I, 3)
-- isResolved(I, 2)

-- Testing the prune map function

-- R = QQ[x,y,z];
-- m = ideal(x,y,z);
-- testcharts = affineCharts(m);
-- f = testcharts#0;
-- Q = target f;
-- prunedringMap(Q);

