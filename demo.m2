needsPackage("Desingularization");
needsPackage("Divisor")
--R = QQ[x,y];
--m = ideal(x,y);

--S = desingStep(R);
--T = blowupCharts(S, m);



-- Checks if the strict transform is smooth in each chart of a Step. 


testRing = QQ[x,y];
D1 = divisor(ideal(y*(y - x^2)));
D2 = divisor(ideal(y*x*(x + y)));
D3 = divisor(x^3*y^4);

-- nonSNCLocus(D1);

cusp = ideal(y^2 - x^3);
cuspresolution = curveResolution(cusp);

-- TBC Make the above work for D1. The recursive step misses multiplicities by taking divisors. 

