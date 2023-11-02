
variableChange = method();
variableChange(PolynomialRing, Symbol) := (R, t) -> (
	oldVars := flatten entries vars R;
	n := #(oldVars);
	coeffRing := coefficientRing(R);
	freshRing := coeffRing[t_1..t_n];
	phi := map(freshRing, R, vars freshRing);
	phi
);

variableChange(PolynomialRing) := R -> (
	variableChange(R, t)
);

variableChange(QuotientRing, Symbol) := (R, t) -> (
	oldVars := flatten entries vars R;
	n := #oldVars;
	coeffRing := coefficientRing(R);
	freshPolyRing := coeffRing[t_1..t_n];
	psi := map(R, freshPolyRing, oldVars);
	freshIdeal = ker psi;
	freshRing := freshPolyRing/freshIdeal;
	phi := map(freshRing, R, vars freshRing);
	phi
);


variableChange(Ideal, Symbol) := (I, t) -> (
	R := ring(I);
	phi = variableChange(R, t);
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
	StructureB = map(B, A, {});
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

-- This function finds the m'th affine chart of the blowup of J, as an A algebra, and the ideal of the exceptional locus. The option allows to just give the chart or to include the exceptional locus.  

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


-- This finds the inverse image ideal. If X' -> X is the blowup, and a is an ideal of X this finds the local descrition of a*O_{X'}.

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

-- Finds the strict transform of I in the m'th chart of the blowup of J. As it is now, it outputs a list. The first element is the exceptional locus, so to get the strict tranform in the usual sense, you look at the second ideal. (Note: this may have more than two elements if I is not irreducible.)

-- T = QQ[x,y];
-- J = ideal(x,y);
-- I = ideal(x^3 - x^2 + y^2);

 -- I defines a nodal cubic resolved by one blow-up at the origin. The following command computes the ideal of the strict transform of I in the first chart.

-- strictTransform(I, J, 1)

isResolved = method(Options => {Exceptional => false});

isResolved(Ideal, ZZ) := opts -> (I, n) -> (

);

-- TODO: make this function! 

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




