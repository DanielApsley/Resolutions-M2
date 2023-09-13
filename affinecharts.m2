affineCharts = method();
affineCharts(Ideal) := J -> (
	A = ring(J);
	I = reesIdeal(J);
	B = ring(I);
	n = #(gens B);
	AffineRing = A[x1..xn];
	listofcharts = {};
	for i from 0 to n  do (
		doubleus = {};
		for j from 0 to (i - 1) do (
			doubleus = append(doubleus, x(j + 1))
		);
		doubleus = append(doubleus, 1);
		for j from (i + 1) to n do (
			doubleus = append(doubleus, xj)
		);
		phi = map(AffineRing,B, doubleus);
		listofcharts = append(listofcharts, phi(I))
	);
);
T = QQ[a,b];
Tdeal= ideal(a,b);
