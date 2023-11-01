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
