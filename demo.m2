needsPackage("Desingularization");
needsPackage("Divisor");
--R = QQ[x,y];
--m = ideal(x,y);

--S = desingStep(R);
--T = blowupCharts(S, m);



-- Checks if the strict transform is smooth in each chart of a Step. 


--testRing = QQ[x,y];
--D1 = divisor(ideal(y*(y - x^2)));
--D2 = divisor(ideal(y*x*(x + y)));
--D3 = divisor(x^3*y^4);

-- nonSNCLocus(D1);

--cusp = ideal(y^2 - x^3);
--cuspresolution = curveResolution(cusp);

-- TBC Make the above work for D1. The recursive step misses multiplicities by taking divisors. 

--R = QQ[x,y];

--I1 = ideal(y-x^2);
--J1 = ideal(y);
--D1 = divisor(I1*J1);
--a1 = nonSNCLocusAlongIdeal(D1,J1); -- expect (x,y)

--I2 = ideal(y-x^2*(x-1));
--J2 = ideal(y);
--D2 = divisor(I2*J2);
--a2 = nonSNCLocusAlongIdeal(D2,J2); -- expect (x,y)

--I3 = ideal((y-2*x)*(y-3*x));
--J3 = ideal(y-x);
--D3 = divisor(I3*J3);
--a3 = nonSNCLocusAlongIdeal(D3,J3); -- expect (x,y)

-- note: press "alt + enter" to run these commands in the terminal w/o copying & pasting
needsPackage("Desingularization");
needsPackage("Divisor");

BaseRing = QQ[x,y]

-- I = ideal(x^2*(1-y^3*x))
-- cusp, should require 2 blow-ups
I = ideal(y^2-x^3);
curveResolution(I)
D = divisor(ideal(y^2-x^5));

s1 = desingStep(D);
locus = nonSNCLocus(s1);
s1#Boundary#0
s1#CheckLoci#0
nonSNCLocusAlongIdeal(s1#Boundary#0,s1#CheckLoci#0)

s2 = blowupCharts(s1,locus#0)
