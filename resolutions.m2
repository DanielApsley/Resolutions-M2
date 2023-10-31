
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


affineCharts = method();
affineCharts(Ideal, ZZ) := (J, m) -> (
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
	prunedringMap(quotient)*projection * structureMap
);

-- This function finds the m'th affine chart of the blowup of J, as an A algebra. 

affineCharts(Ideal) := idealdude -> (
	listofCharts := {};
	for i from 1 to (#(flatten entries gens idealdude)) do (
		 listofCharts = append(listofCharts, affineCharts(idealdude, i))
	);
	listofCharts
);

isLinear = method();
isLinear(Ideal) := J -> (
	dummycounter = 0;
	L := flatten entries (gens J);
	for l in L do (
		if degree(l) == {1} then (
			dummycounter = dummycounter + 1
		);
	);
	dummycounter == #L
);

-- Tests if an ideal of a polynomial ring is cut out by linear equations. May need to take minimal generators of J. For now I only want to consider linear spaces cut out by coordinates.

-- TODO: Find a function which gives a coordinate automorphism which takes any given linear ideal to a coordinate one. (eg. )

linearBlowupVariables = method();
linearBlowupVariables(Ring, ZZ, ZZ, ZZ) := (R, r, n, m) -> (
	if (m > n) or (m < 1) then (
		error "Chart number out of range."
	);
	if (n > r) then (
		error "Not enough variables."
	);
	L := {};
	chartRing := R[w_1..w_r];
	for i from 1 to (n - m) do (
		L = append(L, w_(n - i)*w_(n - m + 1))
	);
	L = append(L, w_(n - m + 1));
	for j from (n - m + 2) to n do (
		L = append(L, w_(n - m + 2)*w_(n - j + 1))
	);
	for k from (n + 1) to r do (
		L = append(L, w_k);
	);
	{chartRing, L}
);

-- This is an auxiliary function encoding the change of variables in the following function. R is the base field (or ring), r is the dimension of the affine space you're blowing up, n is the number of generators of the linear monomial ideal which will be the center of the blowup, and m is the chart. 

linearBlowupChart = method();
linearBlowupChart(Ring, ZZ, ZZ, ZZ) := (R, r, n, m) -> (
	A := R[k_1..k_r];
	masterList := linearBlowupVariables(R, r, n, m);
	chartRing := masterList#0;
	linearBeans := masterList#1;
	phi := map(chartRing, A, linearBeans);
	phi
);

linearBlowupChart(PolynomialRing, ZZ, ZZ) := (A, n, m) -> (
	r = #(gens A);
	R = coefficientRing(A);
	masterList := linearBlowupVariables(R, r, n, m);
	chartRing := masterList#0;
	linearBeans := masterList#1;
	phi := map(chartRing, A, linearBeans);
	phi
);


-- This allows you to change variables from the affine space you're blowing up to the affine space over R resulting from the m'th chart. 

totalTransform = method();

totalTransform(Ideal, Ideal, ZZ) := (I, J, m) -> (
	chartMap := affineCharts(J, m);
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

-- TODO: Make this less useless somehow, or remove it.

totalTransform(Ideal, ZZ, ZZ) := (I, n, m) -> (
	A := ring(I);
	if instance(A, PolynomialRing) == false then (
		error "Expected polynomial ring."
	);
	phi := linearBlowupChart(A, n, m);
    phi(I)
);

totalTransform(Ideal, ZZ) := (I, n) ->  (
    outputlist := {};
	for i from 1 to n do (
		outputlist = append(outputlist, totalTransform(I, n, i));
	);
	outputlist

);

-- This finds the inverse image ideal. If X' -> X is the blowup, and a is an ideal of X this finds the local descrition of a*O_{X'}.

-- This is useful as an auxiliary function and also to compute log resolutions of ideal sheaves.    

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


strictTransform(Ideal, Ideal) := opts -> (I, J) -> (
	n := #(flatten entries gens J);
	L := {};
	for i from 1 to n do (
		littleL := strictTransform(I,J,i,opts);
		L = append(L, littleL);
	);
	L
);


strictTransform(Ideal, ZZ, ZZ) := opts -> (I, n, m) -> (
	idealList := primaryDecomposition(totalTransform(I, n, m));
    if (opts#Exceptional === true) then (
        return idealList;
    );
    if (opts#Exceptional === false) then (
        newidealList := drop(idealList, 1);
        a := newidealList#-1; 
        for b in drop(newidealList, -1) do (
            a = b * a;
        );
        return a;
    );
);

strictTransform(Ideal, ZZ) := opts -> (I, n) -> (
	L := {};
	for i from 1 to n do (
		littleL := strictTransform(I,n,i,opts);
		L = append(L, littleL);
	);
	L
);

-- Finds the strict transform of I in the m'th chart of the blowup of J. As it is now, it outputs a list. The first element is the exceptional locus, so to get the strict tranform in the usual sense, you look at the second ideal. (Note: this may have more than two elements if I is not irreducible.)

-- To use the second version of this function (the better way), take an ideal I of the polynomial ring you want to blow up. Then, n input makes it blow up along the ideal (x_1, x_2, ..., x_n), and m denotes the chart you're looking in. (ie, the m'th standard chart in Proj(Rees Algebra))  

-- T = QQ[x,y];
-- J = ideal(x,y);
-- I = ideal(x^3 - x^2 + y^2);

 -- I defines a nodal cubic resolved by one blow-up at the origin. The following two commands are doing the same calculation: looking at the ideal of the strict transform of I in the first chart. However, the second recognises the chart as living in a polynomial ring rather than a quotient ring (which we know to be isomorphic to a polynomial ring).

-- strictTransform(I, J, 1)
-- strictTransform(I, 2, 1)

isResolved = method(Options => {Exceptional => false});

isResolved(Ideal, ZZ) := opts -> (I, n) -> (
    numsmoothcharts := 0;
    for a in strictTransform(I, n) do (
        if singularLocus(a) == 0 then (
            numsmoothcharts = numsmoothcharts + 1;
        );
    );
    numsmoothcharts == n
);

-- Checks if the locus defined by I is resolved by a single blowup (x_1, .., x_n). Example below. 

-- TODO: Add option functionality to see if the total transform has SNC support. 

-- T = QQ[x,y,z];
-- I = ideal(x^2*z - y^2); -- whitney umbrella

-- isResolved(I, 3)
-- isResolved(I, 2)

-- Testing the prune map function

 R = QQ[x,y,z];
 m = ideal(x,y,z);
 testcharts = affineCharts(m);
 f = testcharts#0;
 Q = target f;
-- prunedringMap(Q);



segreMap = method();

segreMap(PolynomialRing, PolynomialRing) := (R, S) -> (
    if (coefficientRing(R) =!= coefficientRing(S)) then (
        error "Expected same coefficients."
    );
    n := #(flatten entries vars R);
    m := #(flatten entries vars S);
    r := (n + 1)*(m + 1) - 1;
    bigBigraded := R ** S;
    coeff := coefficientRing(R);
    bigProj := coeff[a_0..a_r];
    bigBigraded
)
