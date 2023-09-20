affineCharts = method();
affineCharts(Ideal, ZZ) := (J, m) -> (
	A := ring(J);
	a := reesIdeal(J); -- Ideal of rees algebra in affine space over A.
	B := ring(a);
	structureB = map(B, A, {});
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
	projection * structureMap
);

-- This function finds the m'th affine chart of the blowup of J, as an A algebra. 

affineCharts(Ideal) := idealdude -> (
	listofCharts := {};
	for i from 1 to (#gens idealdude) do (
		 listofCharts = append(listofCharts, affineCharts(idealdude, i))
	);
	listofCharts
);

-- TODO: Fix variable issues so the above runs.

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
		L = append(L, w_(n - m + 1)*w_(n - j + 1))
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

strictTransform = method();

strictTransform(Ideal, Ideal, ZZ) := (I, J, m) -> (
	chartMap := affineCharts(J, m);
	primaryDecomposition(chartMap(I))	
);

strictTransform(Ideal, ZZ, ZZ) := (I, n, m) -> (
	A := ring(I);
	if instance(A, PolynomialRing) == false then (
		error "Expected polynomial ring."
	);
	phi := linearBlowupChart(A, n, m);
	primaryDecomposition(phi(I))
);

-- Finds the strict transform of I in the m'th chart of the blowup of J. As it is now, it outputs a list. The first element is the exceptional locus, so to get the strict tranform in the usual sense, you look at the second ideal. (Note: this may have more than two elements if I is not irreducible.)

-- To use the second version of this function (the better way), take an ideal I of the polynomial ring you want to blow up. Then, n input makes it blow up along the ideal (x_1, x_2, ..., x_n), and m denotes the chart you're looking in. (ie, the m'th standard chart in Proj(Rees Algebra))  

T = QQ[x,y];
J = ideal(x,y);
I = ideal(x^3 - x^2 + y^2);

 -- I defines a nodal cubic resolved by one blow-up at the origin. The following two commands are doing the same calculation: looking at the ideal of the strict transform of I in the first chart. However, the second recognises the chart as living in a polynomial ring rather than a quotient ring (which we know to be isomorphic to a polynomial ring).

-- strictTransform(I, J, 1)
-- strictTransform(I, 2, 1) 
