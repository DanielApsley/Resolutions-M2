affineCharts = method();
affineCharts(Ideal, ZZ) := (J, m) -> (
	A = ring(J);
	I = reesIdeal(J); -- Ideal of rees algebra in affine space over A.
	B = ring(I);
	n = #gens B;
	AffineRing = A[u_1..u_(n - 1)];
	coolBeans = flatten flatten {toList(u_1..u_(m - 1)), 1, toList(u_m..u_(n - 1))};
	phi = map(AffineRing, B, coolBeans);
	phi(I)
);

-- This function finds the m'th affine chart of the blowup of J. 

-- It works, but the variables and letter for your ideal needs to be different from the above. (eg. using a to represent your ideal and x_i to represent the variables in your ambient ring, this should work just fine.)

-- It would be nice to avoid the flatten flatten. Also, I would like to add an error message for when m is too big or small. 

affineCharts(Ideal) := J -> (
	listofCharts = {};
	n = #gens J;
	for i from 1 to n do (
		listofCharts = append(listofCharts, affineCharts(J, i))
	);
	listofCharts
);

-- This however, does not work. It is strange, since you can run the loop manually and it works fine. 


