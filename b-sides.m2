-- A collection of functions and code which may be useful, but is not currently used in resolutions.m2. 

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
-- segreMap is a work in progress. To compute global blowups. 

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

strictTransform = method(Options => {Exceptional => false});

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

-- With these older functions this isResolved method checks if the strict transform of I defines a nonsingular variety.
