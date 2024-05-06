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

-- R = QQ[x,y]
-- step0 = desingStep(R)
-- step1 = blowupCharts(step0, ideal(x,y))

-- R1 = target(step1#Charts#0)
-- m = ideal(T1_1, y)

-- step2 = blowupCharts(step1, m)

-- I = ideal(x^2*(1-y^3*x))
-- cusp, should require 2 blow-ups
-- I = ideal(y^2-x^7);
-- curveResolution(I)
-- D = divisor(ideal(y^2-x^5));

-- s1 = desingStep(D);
-- locus = nonSNCLocus(s1);
-- s1#Boundary#0
-- s1#CheckLoci#0
-- nonSNCLocusAlongIdeal(s1#Boundary#0,s1#CheckLoci#0)

-- s2 = blowupCharts(s1,locus#0)



-- R = QQ[x,y]
-- m = ideal(x,y)

-- step0 = desingStep(R)
-- step1 = blowupCharts(step0, m)

-- peek step1


-- R = QQ[x,y]
-- S = R[t]/ideal(x*t-y)
-- singularLocus(S)

-- To compute D^n for an n dimensional normal projective variety X and a Cartier divisor D. 

R = QQ[x,y,z];
D = divisor(x*y^2 - z^3);
S = projDesingStep(D);

Chartring = target((S#Charts)#0);

m = sub(ideal(y,z), Chartring);

S1 = blowupCharts(S, m);

-- R = QQ[x,y];
-- D = divisor(x^2 - y^3);
-- S = desingStep(D);
-- m = ideal(x,y);
-- S1 = blowupCharts(S, m);

-- R1 = target (S1#Charts)#0;
-- m1 = sub(ideal(T1_1, y), R1);

-- Included here for testing since it won't be exported.

mutaBate = method();

mutaBate(List) := L -> (
    output := new MutableList from L;
    for i from 0 to (#L - 1) do (
        output#i = new MutableList from L#i;
    );
    return output;
);

demutaBate = method();

demutaBate(MutableList) := L -> (
    output := {};
    for i from 0 to (#L - 1) do (
        output = append(output, new List from (L#i));
    );
    return output;
);



