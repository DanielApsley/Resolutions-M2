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
	L = flatten entries (gens J);
	for l in L do (
		if degree(l) == {1} then (
			dummycounter = dummycounter + 1
		);
	);
	dummycounter == #L
);

-- Tests if an ideal of a polynomial ring is cut out by linear equations. May need to take minimal generators of J. For now I only want to consider linear spaces cut out by coordinates.

-- TODO: Find a function which gives a coordinate automorphism which takes any given linear ideal to a coordinate one. (eg. )

linearBlowupChart = method();
linearBlowupChart(Ideal, ZZ) := (J, m) -> (
	if isLinear(J) == false then (
		error "Expected linear ideal";
	);
	"TBC" 
);

-- The intention here is to output actual charts: regular isomorphism from an affine space. As such, this is reserved for blowing up linear ideals of affine space. This will hopefully have the benefit of being iterative, and more appropriate for taking strict tranforms.  


strictTransform = method();

strictTransform(Ideal, Ideal, ZZ) := (I, J, m) -> (
	chartMap := affineCharts(J, m);
	primaryDecomposition(chartMap(I))	
);

-- Finds the strict transform of I in the m'th chart of the blowup of J. As it is now, it outputs a list. The first element is the exceptional locus, so to get the strict tranform in the usual sense, you look at the second ideal. 

-- TODO: Find a way to make the generators less redundant. 

T = QQ[x,y];
J = ideal(x,y);
I = ideal(x^3 - x^2 + y^2); -- nodal cubic resolved by one blow-up at the origin. 
