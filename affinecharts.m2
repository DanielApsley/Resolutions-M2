affineCharts = method();
affineCharts(Ideal, ZZ) := (J, m) -> (
	A := ring(J);
	a := reesIdeal(J); -- Ideal of rees algebra in affine space over A.
	B := ring(a);
	n := #gens B;
	AffineRing := A[u_1..u_(n - 1)];
	structureMap := map(AffineRing, A, {});
	coolBeans := flatten flatten {toList(u_1..u_(m - 1)), 1, toList(u_m..u_(n - 1))};
	phi := map(AffineRing, B, coolBeans);
	quotient := AffineRing/phi(a);
	projection := map(quotient, AffineRing, {});
	projection * structureMap
);

-- This function finds the m'th affine chart of the blowup of J, as an A algebra. 

-- TODO: Add an option to output just the ideal, make an error message when m is not in the allowed range. 

affineCharts(Ideal) := idealdude -> (
	listofCharts := {};
	for i from 1 to (#gens idealdude) do (
		 listofCharts = append(listofCharts, affineCharts(idealdude, i))
	);
	listofCharts
);

-- TODO: Fix variable issues so the above runs.

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
