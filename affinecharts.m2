affineCharts = method();
affineCharts(Ideal, ZZ) := (J, m) -> (
	A := ring(J);
	a := reesIdeal(J); -- Ideal of rees algebra in affine space over A.
	B := ring(a);
	n := #gens B;
	AffineRing := A[u_1..u_(n - 1)];
	coolBeans := flatten flatten {toList(u_1..u_(m - 1)), 1, toList(u_m..u_(n - 1))};
	phi := map(AffineRing, B, coolBeans);
	phi(a)
);

-- This function finds the m'th affine chart of the blowup of J. 

-- It works, but the variables and letter for your ideal needs to be different from the above. (eg. If you use I to represent your ideal and x_i to represent the variables in your ambient ring, this should work just fine.)

-- It would be nice to avoid the flatten flatten. Also, I would like to add an error message for when m is too big or small. 

affineCharts(Ideal) := idealdude -> (
	listofCharts := {};
	for i from 1 to (#gens idealdude) do (
		 listofCharts = append(listofCharts, affineCharts(idealdude, i))
	);
	listofCharts
);

-- This however, does not work. It is strange, since you can run the loop manually and it works fine.

T = QQ[x,y,z];
I = ideal(x^2, y, z);

strictTransform = method();

strictTransform(Ideal, ZZ) := (J, m) -> (

);

